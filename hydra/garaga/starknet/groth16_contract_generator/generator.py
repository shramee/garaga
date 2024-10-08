import os
import subprocess
from enum import Enum

from garaga.definitions import CurveID, G1G2Pair, G1Point, G2Point
from garaga.modulo_circuit_structs import E12D, G2Line, StructArray
from garaga.precompiled_circuits.multi_miller_loop import (
    MultiMillerLoopCircuit,
    precompute_lines,
)
from garaga.starknet.groth16_contract_generator.parsing_utils import (
    Groth16Proof,
    Groth16VerifyingKey,
)
from garaga.starknet.starknet_cli import create_directory


class ECIP_OPS_CLASS_HASH(Enum):
    MAINNET = None
    SEPOLIA = 0x0245A22F0FE79CFF1A66622EF3A1B545DD109E159C7138CC3B6C224782DBD6D8


def precompute_lines_from_vk(vk: Groth16VerifyingKey) -> StructArray:

    # Precompute lines for fixed G2 points
    lines = precompute_lines([vk.gamma, vk.delta])
    precomputed_lines = StructArray(
        name="lines",
        elmts=[
            G2Line(name=f"line{i}", elmts=lines[i : i + 4])
            for i in range(0, len(lines), 4)
        ],
    )

    return precomputed_lines


def gen_groth16_verifier(
    vk_path: str,
    output_folder_path: str,
    output_folder_name: str,
    ecip_class_hash: ECIP_OPS_CLASS_HASH,
) -> str:
    vk = Groth16VerifyingKey.from_json(vk_path)
    curve_id = vk.curve_id
    output_folder_name = output_folder_name + f"_{curve_id.name.lower()}"
    output_folder_path = os.path.join(output_folder_path, output_folder_name)

    precomputed_lines = precompute_lines_from_vk(vk)

    constants_code = f"""
    use garaga::definitions::{{G1Point, G2Point, E12D, G2Line, u384}};
    use garaga::groth16::Groth16VerifyingKey;

    pub const N_PUBLIC_INPUTS:usize = {len(vk.ic)-1};
    {vk.serialize_to_cairo()}
    pub const precomputed_lines: [G2Line; {len(precomputed_lines)//4}] = {precomputed_lines.serialize(raw=True, const=True)};
    """

    contract_code = f"""
use garaga::definitions::E12DMulQuotient;
use garaga::groth16::{{Groth16Proof, MPCheckHint{curve_id.name}}};
use super::groth16_verifier_constants::{{N_PUBLIC_INPUTS, vk, ic, precomputed_lines}};

#[starknet::interface]
trait IGroth16Verifier{curve_id.name}<TContractState> {{
    fn verify_groth16_proof_{curve_id.name.lower()}(
        ref self: TContractState,
        groth16_proof: Groth16Proof,
        mpcheck_hint: MPCheckHint{curve_id.name},
        small_Q: E12DMulQuotient,
        msm_hint: Array<felt252>,
    ) -> bool;
}}

#[starknet::contract]
mod Groth16Verifier{curve_id.name} {{
    use starknet::SyscallResultTrait;
    use garaga::definitions::{{G1Point, G1G2Pair, E12DMulQuotient}};
    use garaga::groth16::{{multi_pairing_check_{curve_id.name.lower()}_3P_2F_with_extra_miller_loop_result, Groth16Proof, MPCheckHint{curve_id.name}}};
    use garaga::ec_ops::{{G1PointTrait, G2PointTrait, ec_safe_add}};
    use super::{{N_PUBLIC_INPUTS, vk, ic, precomputed_lines}};

    const ECIP_OPS_CLASS_HASH: felt252 = {ecip_class_hash.value};

    #[storage]
    struct Storage {{}}

    #[abi(embed_v0)]
    impl IGroth16Verifier{curve_id.name} of super::IGroth16Verifier{curve_id.name}<ContractState> {{
        fn verify_groth16_proof_{curve_id.name.lower()}(
            ref self: ContractState,
            groth16_proof: Groth16Proof,
            mpcheck_hint: MPCheckHint{curve_id.name},
            small_Q: E12DMulQuotient,
            msm_hint: Array<felt252>,
        ) -> bool {{
            groth16_proof.a.assert_on_curve({curve_id.value});
            groth16_proof.b.assert_on_curve({curve_id.value});
            groth16_proof.c.assert_on_curve({curve_id.value});

            let ic = ic.span();

            let vk_x: G1Point = match ic.len() {{
                0 => panic!("Malformed VK"),
                1 => *ic.at(0),
                _ => {{
                    // Start serialization with the hint array directly to avoid copying it.
                    let mut msm_calldata: Array<felt252> = msm_hint;
                    // Add the points from VK and public inputs to the proof.
                    Serde::serialize(@ic.slice(1, N_PUBLIC_INPUTS), ref msm_calldata);
                    Serde::serialize(@groth16_proof.public_inputs, ref msm_calldata);
                    // Complete with the curve indentifier ({curve_id.value} for {curve_id.name}):
                    msm_calldata.append({curve_id.value});

                    // Call the multi scalar multiplication endpoint on the Garaga ECIP ops contract
                    // to obtain vk_x.
                    let mut _vx_x_serialized = core::starknet::syscalls::library_call_syscall(
                        ECIP_OPS_CLASS_HASH.try_into().unwrap(),
                        selector!("msm_g1"),
                        msm_calldata.span()
                    )
                        .unwrap_syscall();

                    ec_safe_add(
                        Serde::<G1Point>::deserialize(ref _vx_x_serialized).unwrap(), *ic.at(0), {curve_id.value}
                    )
                }}
            }};
            // Perform the pairing check.
            multi_pairing_check_{curve_id.name.lower()}_3P_2F_with_extra_miller_loop_result(
                G1G2Pair {{ p: vk_x, q: vk.gamma_g2 }},
                G1G2Pair {{ p: groth16_proof.c, q: vk.delta_g2 }},
                G1G2Pair {{ p: groth16_proof.a.negate({curve_id.value}), q: groth16_proof.b }},
                vk.alpha_beta_miller_loop_result,
                precomputed_lines.span(),
                mpcheck_hint,
                small_Q
            )
        }}
    }}
}}


    """

    create_directory(output_folder_path)
    src_dir = os.path.join(output_folder_path, "src")
    create_directory(src_dir)

    with open(os.path.join(src_dir, "groth16_verifier_constants.cairo"), "w") as f:
        f.write(constants_code)

    with open(os.path.join(src_dir, "groth16_verifier.cairo"), "w") as f:
        f.write(contract_code)

    with open(os.path.join(output_folder_path, "Scarb.toml"), "w") as f:
        f.write(
            f"""
[package]
name = "groth16_example_{curve_id.name.lower()}"
version = "0.1.0"
edition = "2024_07"

[dependencies]
garaga = {{ path = "../../" }}
starknet = "2.7.0"

[cairo]
sierra-replace-ids = false

[[target.starknet-contract]]
casm = true
casm-add-pythonic-hints = true
"""
        )

    with open(os.path.join(src_dir, "lib.cairo"), "w") as f:
        f.write(
            f"""
mod groth16_verifier;
mod groth16_verifier_constants;
"""
        )
    subprocess.run(["scarb", "fmt"], check=True, cwd=output_folder_path)
    return constants_code


if __name__ == "__main__":

    BN_VK_PATH = (
        "hydra/garaga/starknet/groth16_contract_generator/examples/vk_bn254.json"
    )
    BLS_VK_PATH = (
        "hydra/garaga/starknet/groth16_contract_generator/examples/vk_bls.json"
    )

    CONTRACTS_FOLDER = "src/cairo/contracts/"  # Do not change this

    FOLDER_NAME = "groth16_example"  # '_curve_id' is appended in the end.

    gen_groth16_verifier(
        BN_VK_PATH, CONTRACTS_FOLDER, FOLDER_NAME, ECIP_OPS_CLASS_HASH.SEPOLIA
    )
    gen_groth16_verifier(
        BLS_VK_PATH, CONTRACTS_FOLDER, FOLDER_NAME, ECIP_OPS_CLASS_HASH.SEPOLIA
    )
