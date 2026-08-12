use core::circuit::{
    CircuitElement, CircuitElement as CE, CircuitInput, CircuitInput as CI, CircuitInputs,
    CircuitModulus, CircuitOutputsTrait, EvalCircuitTrait, circuit_add, circuit_inverse,
    circuit_mul, circuit_sub, u384, u96,
};
use core::num::traits::Zero;
use corelib_imports::bounded_int::upcast;
use garaga::core::circuit::{AddInputResultTrait2, u288IntoCircuitInputValue};
use garaga::definitions::{E12D, get_BLS12_381_modulus, get_BN254_modulus, u288};
use garaga::utils::hashing::{PoseidonState, hades_permutation, hash_quadruple_u288};

const POW_2_32_252: felt252 = 0x100000000;
const POW_2_64_252: felt252 = 0x10000000000000000;

const POW_2_256_384: u384 = u384 { limb0: 0x0, limb1: 0x0, limb2: 0x10000000000000000, limb3: 0x0 };

// Reduces a u384 given a circuit modulus by computing (a + 0) mod p.
// Circuits outputs are reduced mod p.
pub fn reduce_mod_p(a: u384, modulus: CircuitModulus) -> u384 {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let in2 = CircuitElement::<CircuitInput<1>> {};
    let reduce = circuit_add(in1, in2);

    let outputs = (reduce,)
        .new_inputs()
        .next_2(a)
        .next_2([0, 0, 0, 0])
        .done_2()
        .eval(modulus)
        .unwrap();

    return outputs.get_output(reduce);
}

pub fn neg_mod_p(a: u384, modulus: CircuitModulus) -> u384 {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let in2 = CircuitElement::<CircuitInput<1>> {};
    let neg = circuit_sub(in1, in2);

    let outputs = (neg,)
        .new_inputs()
        .next_2([0, 0, 0, 0])
        .next_2(a)
        .done_2()
        .eval(modulus)
        .unwrap();

    return outputs.get_output(neg);
}

// Returns true if a == -b mod p (a + b = 0 mod p)
pub fn is_opposite_mod_p(a: u384, b: u384, modulus: CircuitModulus) -> bool {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let in2 = CircuitElement::<CircuitInput<1>> {};
    let sum = circuit_add(in1, in2);
    let outputs = (sum,).new_inputs().next_2(a).next_2(b).done_2().eval(modulus).unwrap();

    return outputs.get_output(sum).is_zero();
}

// Returns true if a == 0 mod p (p must be odd prime)
pub fn is_zero_mod_p(a: u384, modulus: CircuitModulus) -> bool {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let sum = circuit_add(in1, in1);
    let outputs = (sum,).new_inputs().next_2(a).done_2().eval(modulus).unwrap();
    return outputs.get_output(sum).is_zero();
}

pub fn is_even_u384(a: u384) -> bool {
    let limb0_u128: u128 = upcast(a.limb0);
    limb0_u128 % 2 == 0
}


pub fn u32_8_to_u384(a: [u32; 8]) -> u384 {
    let [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7] = a;
    let l0: felt252 = a_7.into() + a_6.into() * POW_2_32_252 + a_5.into() * POW_2_64_252;
    let l1: felt252 = a_4.into() + a_3.into() * POW_2_32_252 + a_2.into() * POW_2_64_252;
    let l2: felt252 = a_1.into() + a_0.into() * POW_2_32_252;
    u384 {
        limb0: l0.try_into().unwrap(),
        limb1: l1.try_into().unwrap(),
        limb2: l2.try_into().unwrap(),
        limb3: 0,
    }
}

// Takes big endian u512 and returns a u384 mod modulus
// u512 = low_256 + high_256 * 2^256
// u512 % p = (low_256 + high_256 * 2^256) % p
// = (low_256 % p + high_256 * 2^256 % p) % p
// CAUTION : a_high and a_low are expected to be < 2^256. No check is performed.
pub fn u512_mod_p(high_256: u384, low_256: u384, modulus: CircuitModulus) -> u384 {
    let low = CircuitElement::<CircuitInput<0>> {};
    let high = CircuitElement::<CircuitInput<1>> {};
    let shift = CircuitElement::<CircuitInput<2>> {};
    let high_shifted = circuit_mul(high, shift);
    let res = circuit_add(low, high_shifted);

    let outputs = (res,)
        .new_inputs()
        .next_2(low_256)
        .next_2(high_256)
        .next_2(POW_2_256_384)
        .done_2()
        .eval(modulus)
        .unwrap();

    return outputs.get_output(res);
}

pub fn add_mod_p(a: u384, b: u384, modulus: CircuitModulus) -> u384 {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let in2 = CircuitElement::<CircuitInput<1>> {};
    let add = circuit_add(in1, in2);

    let outputs = (add,).new_inputs().next_2(a).next_2(b).done_2().eval(modulus).unwrap();

    return outputs.get_output(add);
}

pub fn sub_mod_p(a: u384, b: u384, modulus: CircuitModulus) -> u384 {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let in2 = CircuitElement::<CircuitInput<1>> {};
    let sub = circuit_sub(in1, in2);

    let outputs = (sub,).new_inputs().next_2(a).next_2(b).done_2().eval(modulus).unwrap();

    return outputs.get_output(sub);
}

pub fn mul_mod_p(a: u384, b: u384, modulus: CircuitModulus) -> u384 {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let in2 = CircuitElement::<CircuitInput<1>> {};
    let mul = circuit_mul(in1, in2);

    let outputs = (mul,).new_inputs().next_2(a).next_2(b).done_2().eval(modulus).unwrap();

    return outputs.get_output(mul);
}

#[inline(always)]
pub fn batch_3_mod_p(x: u384, y: u384, z: u384, c0: u384, modulus: CircuitModulus) -> u384 {
    let _x = CircuitElement::<CircuitInput<0>> {};
    let _y = CircuitElement::<CircuitInput<1>> {};
    let _z = CircuitElement::<CircuitInput<2>> {};
    let _c0 = CircuitElement::<CircuitInput<3>> {};
    let _c1 = circuit_mul(_c0, _c0);
    let _c2 = circuit_mul(_c1, _c0);
    let _mul1 = circuit_mul(_x, _c0);
    let _mul2 = circuit_mul(_y, _c1);
    let _mul3 = circuit_mul(_z, _c2);
    let res = circuit_add(circuit_add(_mul1, _mul2), _mul3);

    let outputs = (res,)
        .new_inputs()
        .next_2(x)
        .next_2(y)
        .next_2(z)
        .next_2(c0)
        .done_2()
        .eval(modulus)
        .unwrap();

    return outputs.get_output(res);
}


pub fn inv_mod_p(a: u384, modulus: CircuitModulus) -> u384 {
    let in1 = CircuitElement::<CircuitInput<0>> {};
    let inv = circuit_inverse(in1);

    let outputs = (inv,).new_inputs().next_2(a).done_2().eval(modulus).unwrap();

    return outputs.get_output(inv);
}


#[inline(always)]
pub fn eval_and_hash_E12D_u288_transcript(
    transcript: Span<E12D<u288>>, mut s: PoseidonState, z: u384,
) -> (PoseidonState, Array<u384>) {
    let base: felt252 = 79228162514264337593543950336; // 2**96
    let mut evals: Array<u384> = array![];
    let modulus = get_BN254_modulus(); // BN254 prime field modulus

    for elmt in transcript {
        let elmt = *elmt;
        let _s = hash_quadruple_u288(elmt.w0, elmt.w1, elmt.w2, elmt.w3, base, s);
        let _s = hash_quadruple_u288(elmt.w4, elmt.w5, elmt.w6, elmt.w7, base, _s);
        let _s = hash_quadruple_u288(elmt.w8, elmt.w9, elmt.w10, elmt.w11, base, _s);
        s = _s;

        let (in0, in1, in2) = (CE::<CI<0>> {}, CE::<CI<1>> {}, CE::<CI<2>> {});
        let (in3, in4, in5) = (CE::<CI<3>> {}, CE::<CI<4>> {}, CE::<CI<5>> {});
        let (in6, in7, in8) = (CE::<CI<6>> {}, CE::<CI<7>> {}, CE::<CI<8>> {});
        let (in9, in10, in11) = (CE::<CI<9>> {}, CE::<CI<10>> {}, CE::<CI<11>> {});
        let in12 = CE::<CI<12>> {};
        let t0 = circuit_mul(in11, in12); // Eval X Horner step: multiply by z
        let t1 = circuit_add(in10, t0); // Eval X Horner step: add coefficient_10
        let t2 = circuit_mul(t1, in12); // Eval X Horner step: multiply by z
        let t3 = circuit_add(in9, t2); // Eval X Horner step: add coefficient_9
        let t4 = circuit_mul(t3, in12); // Eval X Horner step: multiply by z
        let t5 = circuit_add(in8, t4); // Eval X Horner step: add coefficient_8
        let t6 = circuit_mul(t5, in12); // Eval X Horner step: multiply by z
        let t7 = circuit_add(in7, t6); // Eval X Horner step: add coefficient_7
        let t8 = circuit_mul(t7, in12); // Eval X Horner step: multiply by z
        let t9 = circuit_add(in6, t8); // Eval X Horner step: add coefficient_6
        let t10 = circuit_mul(t9, in12); // Eval X Horner step: multiply by z
        let t11 = circuit_add(in5, t10); // Eval X Horner step: add coefficient_5
        let t12 = circuit_mul(t11, in12); // Eval X Horner step: multiply by z
        let t13 = circuit_add(in4, t12); // Eval X Horner step: add coefficient_4
        let t14 = circuit_mul(t13, in12); // Eval X Horner step: multiply by z
        let t15 = circuit_add(in3, t14); // Eval X Horner step: add coefficient_3
        let t16 = circuit_mul(t15, in12); // Eval X Horner step: multiply by z
        let t17 = circuit_add(in2, t16); // Eval X Horner step: add coefficient_2
        let t18 = circuit_mul(t17, in12); // Eval X Horner step: multiply by z
        let t19 = circuit_add(in1, t18); // Eval X Horner step: add coefficient_1
        let t20 = circuit_mul(t19, in12); // Eval X Horner step: multiply by z
        let t21 = circuit_add(in0, t20); // Eval X Horner step: add coefficient_0

        let mut circuit_inputs = (t21,).new_inputs();
        // Prefill constants:

        // Fill inputs:
        circuit_inputs = circuit_inputs.next_2(elmt.w0); // in0
        circuit_inputs = circuit_inputs.next_2(elmt.w1); // in1
        circuit_inputs = circuit_inputs.next_2(elmt.w2); // in2
        circuit_inputs = circuit_inputs.next_2(elmt.w3); // in3
        circuit_inputs = circuit_inputs.next_2(elmt.w4); // in4
        circuit_inputs = circuit_inputs.next_2(elmt.w5); // in5
        circuit_inputs = circuit_inputs.next_2(elmt.w6); // in6
        circuit_inputs = circuit_inputs.next_2(elmt.w7); // in7
        circuit_inputs = circuit_inputs.next_2(elmt.w8); // in8
        circuit_inputs = circuit_inputs.next_2(elmt.w9); // in9
        circuit_inputs = circuit_inputs.next_2(elmt.w10); // in10
        circuit_inputs = circuit_inputs.next_2(elmt.w11); // in11
        circuit_inputs = circuit_inputs.next_2(z); // in12

        let outputs = circuit_inputs.done_2().eval(modulus).unwrap();
        let f_of_z: u384 = outputs.get_output(t21);
        evals.append(f_of_z);
    }
    return (s, evals);
}

#[inline(always)]
pub fn eval_and_hash_E12D_u384_transcript(
    transcript: Span<E12D<u384>>, mut s: PoseidonState, z: u384,
) -> (PoseidonState, Array<u384>) {
    let base: felt252 = 79228162514264337593543950336; // 2**96
    let mut evals: Array<u384> = array![];
    let modulus = get_BLS12_381_modulus(); // BLS12_381 prime field modulus

    for elmt in transcript {
        let elmt = *elmt;
        let in_1 = s.s0 + elmt.w0.limb0.into() + base * elmt.w0.limb1.into();
        let in_2 = s.s1 + elmt.w0.limb2.into() + base * elmt.w0.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, s.s2);
        let in_1 = _s0 + elmt.w1.limb0.into() + base * elmt.w1.limb1.into();
        let in_2 = _s1 + elmt.w1.limb2.into() + base * elmt.w1.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w2.limb0.into() + base * elmt.w2.limb1.into();
        let in_2 = _s1 + elmt.w2.limb2.into() + base * elmt.w2.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w3.limb0.into() + base * elmt.w3.limb1.into();
        let in_2 = _s1 + elmt.w3.limb2.into() + base * elmt.w3.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w4.limb0.into() + base * elmt.w4.limb1.into();
        let in_2 = _s1 + elmt.w4.limb2.into() + base * elmt.w4.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w5.limb0.into() + base * elmt.w5.limb1.into();
        let in_2 = _s1 + elmt.w5.limb2.into() + base * elmt.w5.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w6.limb0.into() + base * elmt.w6.limb1.into();
        let in_2 = _s1 + elmt.w6.limb2.into() + base * elmt.w6.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w7.limb0.into() + base * elmt.w7.limb1.into();
        let in_2 = _s1 + elmt.w7.limb2.into() + base * elmt.w7.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w8.limb0.into() + base * elmt.w8.limb1.into();
        let in_2 = _s1 + elmt.w8.limb2.into() + base * elmt.w8.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w9.limb0.into() + base * elmt.w9.limb1.into();
        let in_2 = _s1 + elmt.w9.limb2.into() + base * elmt.w9.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w10.limb0.into() + base * elmt.w10.limb1.into();
        let in_2 = _s1 + elmt.w10.limb2.into() + base * elmt.w10.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);
        let in_1 = _s0 + elmt.w11.limb0.into() + base * elmt.w11.limb1.into();
        let in_2 = _s1 + elmt.w11.limb2.into() + base * elmt.w11.limb3.into();
        let (_s0, _s1, _s2) = hades_permutation(in_1, in_2, _s2);

        s = PoseidonState { s0: _s0, s1: _s1, s2: _s2 };

        let (in0, in1, in2) = (CE::<CI<0>> {}, CE::<CI<1>> {}, CE::<CI<2>> {});
        let (in3, in4, in5) = (CE::<CI<3>> {}, CE::<CI<4>> {}, CE::<CI<5>> {});
        let (in6, in7, in8) = (CE::<CI<6>> {}, CE::<CI<7>> {}, CE::<CI<8>> {});
        let (in9, in10, in11) = (CE::<CI<9>> {}, CE::<CI<10>> {}, CE::<CI<11>> {});
        let in12 = CE::<CI<12>> {};
        let t0 = circuit_mul(in11, in12); // Eval X Horner step: multiply by z
        let t1 = circuit_add(in10, t0); // Eval X Horner step: add coefficient_10
        let t2 = circuit_mul(t1, in12); // Eval X Horner step: multiply by z
        let t3 = circuit_add(in9, t2); // Eval X Horner step: add coefficient_9
        let t4 = circuit_mul(t3, in12); // Eval X Horner step: multiply by z
        let t5 = circuit_add(in8, t4); // Eval X Horner step: add coefficient_8
        let t6 = circuit_mul(t5, in12); // Eval X Horner step: multiply by z
        let t7 = circuit_add(in7, t6); // Eval X Horner step: add coefficient_7
        let t8 = circuit_mul(t7, in12); // Eval X Horner step: multiply by z
        let t9 = circuit_add(in6, t8); // Eval X Horner step: add coefficient_6
        let t10 = circuit_mul(t9, in12); // Eval X Horner step: multiply by z
        let t11 = circuit_add(in5, t10); // Eval X Horner step: add coefficient_5
        let t12 = circuit_mul(t11, in12); // Eval X Horner step: multiply by z
        let t13 = circuit_add(in4, t12); // Eval X Horner step: add coefficient_4
        let t14 = circuit_mul(t13, in12); // Eval X Horner step: multiply by z
        let t15 = circuit_add(in3, t14); // Eval X Horner step: add coefficient_3
        let t16 = circuit_mul(t15, in12); // Eval X Horner step: multiply by z
        let t17 = circuit_add(in2, t16); // Eval X Horner step: add coefficient_2
        let t18 = circuit_mul(t17, in12); // Eval X Horner step: multiply by z
        let t19 = circuit_add(in1, t18); // Eval X Horner step: add coefficient_1
        let t20 = circuit_mul(t19, in12); // Eval X Horner step: multiply by z
        let t21 = circuit_add(in0, t20); // Eval X Horner step: add coefficient_0

        let mut circuit_inputs = (t21,).new_inputs();
        // Prefill constants:

        // Fill inputs:
        circuit_inputs = circuit_inputs.next_2(elmt.w0); // in0
        circuit_inputs = circuit_inputs.next_2(elmt.w1); // in1
        circuit_inputs = circuit_inputs.next_2(elmt.w2); // in2
        circuit_inputs = circuit_inputs.next_2(elmt.w3); // in3
        circuit_inputs = circuit_inputs.next_2(elmt.w4); // in4
        circuit_inputs = circuit_inputs.next_2(elmt.w5); // in5
        circuit_inputs = circuit_inputs.next_2(elmt.w6); // in6
        circuit_inputs = circuit_inputs.next_2(elmt.w7); // in7
        circuit_inputs = circuit_inputs.next_2(elmt.w8); // in8
        circuit_inputs = circuit_inputs.next_2(elmt.w9); // in9
        circuit_inputs = circuit_inputs.next_2(elmt.w10); // in10
        circuit_inputs = circuit_inputs.next_2(elmt.w11); // in11
        circuit_inputs = circuit_inputs.next_2(z); // in12

        let outputs = circuit_inputs.done_2().eval(modulus).unwrap();
        let f_of_z: u384 = outputs.get_output(t21);
        evals.append(f_of_z);
    }
    return (s, evals);
}

// --- Unreduced polynomial evaluation helpers ---
//
// Each number is treated as a polynomial in X = 2^96 with u96 limbs as coefficients.
// "Unreduced" means we skip modular reduction and keep the full outer-product
// representation so callers can verify the result via a Schwartz-Zippel identity check.

// Extract the lower 3 limbs of a u384 as a u288.
// Valid for BN254 field elements, which are always < p < 2^288 (limb3 == 0).
#[inline(always)]
fn u384_low3(a: u384) -> u288 {
    u288 { limb0: a.limb0, limb1: a.limb1, limb2: a.limb2 }
}

// Element-wise addition of two [felt252; 9] outer-product arrays.
#[inline(always)]
fn add9(a: [felt252; 9], b: [felt252; 9]) -> [felt252; 9] {
    let [a0, a1, a2, a3, a4, a5, a6, a7, a8] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7, b8] = b;
    [a0 + b0, a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5, a6 + b6, a7 + b7, a8 + b8]
}

// Element-wise addition of two [felt252; 16] outer-product arrays.
#[inline(always)]
fn add16(a: [felt252; 16], b: [felt252; 16]) -> [felt252; 16] {
    let [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] = b;
    [
        a0 + b0, a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5, a6 + b6, a7 + b7, a8 + b8,
        a9 + b9, a10 + b10, a11 + b11, a12 + b12, a13 + b13, a14 + b14, a15 + b15,
    ]
}

// Multiply two u288 values without modular reduction.
// Returns the 3x3 outer product of their u96 limbs cast to felt252.
// Layout: result[3*i + j] = a.limb[i] * b.limb[j].
// For any scalar x: sum_{i,j} result[3*i+j] * x^(i+j) = a(x) * b(x)
// where a(x) = a.limb0 + a.limb1*x + a.limb2*x^2.
#[inline(always)]
pub fn unreduced_mul_u288(a: u288, b: u288) -> [felt252; 9] {
    let (a0, a1, a2): (felt252, felt252, felt252) = (
        a.limb0.into(), a.limb1.into(), a.limb2.into(),
    );
    let (b0, b1, b2): (felt252, felt252, felt252) = (
        b.limb0.into(), b.limb1.into(), b.limb2.into(),
    );
    [a0 * b0, a0 * b1, a0 * b2, a1 * b0, a1 * b1, a1 * b2, a2 * b0, a2 * b1, a2 * b2]
}

// Multiply two u384 values without modular reduction.
// Returns the 4x4 outer product of their u96 limbs cast to felt252.
// Layout: result[4*i + j] = a.limb[i] * b.limb[j].
// For any scalar x: sum_{i,j} result[4*i+j] * x^(i+j) = a(x) * b(x).
#[inline(always)]
pub fn unreduced_mul_u384(a: u384, b: u384) -> [felt252; 16] {
    let (a0, a1, a2, a3): (felt252, felt252, felt252, felt252) = (
        a.limb0.into(), a.limb1.into(), a.limb2.into(), a.limb3.into(),
    );
    let (b0, b1, b2, b3): (felt252, felt252, felt252, felt252) = (
        b.limb0.into(), b.limb1.into(), b.limb2.into(), b.limb3.into(),
    );
    [
        a0 * b0, a0 * b1, a0 * b2, a0 * b3, a1 * b0, a1 * b1, a1 * b2, a1 * b3, a2 * b0,
        a2 * b1, a2 * b2, a2 * b3, a3 * b0, a3 * b1, a3 * b2, a3 * b3,
    ]
}

// Evaluate E12D<u288> unreduced, accumulating per-term outer products.
// z_powers[i] = z^(i+1) as u384 (limb3 must be 0 for BN254 field elements).
// For any scalar x: evaluating the result gives f(x) = sum_i f.wi(x) * z^i(x).
#[inline(always)]
pub fn eval_e12d_u288(f: E12D<u288>, z_powers: Span<u384>) -> [felt252; 9] {
    let one = u288 { limb0: 1, limb1: 0, limb2: 0 };
    let mut acc = unreduced_mul_u288(f.w0, one);
    acc = add9(acc, unreduced_mul_u288(f.w1, u384_low3(*z_powers.at(0))));
    acc = add9(acc, unreduced_mul_u288(f.w2, u384_low3(*z_powers.at(1))));
    acc = add9(acc, unreduced_mul_u288(f.w3, u384_low3(*z_powers.at(2))));
    acc = add9(acc, unreduced_mul_u288(f.w4, u384_low3(*z_powers.at(3))));
    acc = add9(acc, unreduced_mul_u288(f.w5, u384_low3(*z_powers.at(4))));
    acc = add9(acc, unreduced_mul_u288(f.w6, u384_low3(*z_powers.at(5))));
    acc = add9(acc, unreduced_mul_u288(f.w7, u384_low3(*z_powers.at(6))));
    acc = add9(acc, unreduced_mul_u288(f.w8, u384_low3(*z_powers.at(7))));
    acc = add9(acc, unreduced_mul_u288(f.w9, u384_low3(*z_powers.at(8))));
    acc = add9(acc, unreduced_mul_u288(f.w10, u384_low3(*z_powers.at(9))));
    acc = add9(acc, unreduced_mul_u288(f.w11, u384_low3(*z_powers.at(10))));
    acc
}

// Evaluate E12D<u384> unreduced.
// z_powers[i] = z^(i+1) as u384 (BLS12-381 field elements).
#[inline(always)]
pub fn eval_e12d_u384(f: E12D<u384>, z_powers: Span<u384>) -> [felt252; 16] {
    let one = u384 { limb0: 1, limb1: 0, limb2: 0, limb3: 0 };
    let mut acc = unreduced_mul_u384(f.w0, one);
    acc = add16(acc, unreduced_mul_u384(f.w1, *z_powers.at(0)));
    acc = add16(acc, unreduced_mul_u384(f.w2, *z_powers.at(1)));
    acc = add16(acc, unreduced_mul_u384(f.w3, *z_powers.at(2)));
    acc = add16(acc, unreduced_mul_u384(f.w4, *z_powers.at(3)));
    acc = add16(acc, unreduced_mul_u384(f.w5, *z_powers.at(4)));
    acc = add16(acc, unreduced_mul_u384(f.w6, *z_powers.at(5)));
    acc = add16(acc, unreduced_mul_u384(f.w7, *z_powers.at(6)));
    acc = add16(acc, unreduced_mul_u384(f.w8, *z_powers.at(7)));
    acc = add16(acc, unreduced_mul_u384(f.w9, *z_powers.at(8)));
    acc = add16(acc, unreduced_mul_u384(f.w10, *z_powers.at(9)));
    acc = add16(acc, unreduced_mul_u384(f.w11, *z_powers.at(10)));
    acc
}

// Evaluate a big_Q polynomial (Span<u288>) unreduced.
// q[0] is the constant term; z_powers[i] = z^(i+1) as u384 (limb3 must be 0 for BN254).
pub fn eval_big_Q_u288(q: Span<u288>, z_powers: Span<u384>) -> [felt252; 9] {
    let one = u288 { limb0: 1, limb1: 0, limb2: 0 };
    let mut acc = unreduced_mul_u288(*q.at(0), one);
    let mut i: usize = 1;
    let len = q.len();
    while i < len {
        acc = add9(acc, unreduced_mul_u288(*q.at(i), u384_low3(*z_powers.at(i - 1))));
        i += 1;
    };
    acc
}

// Evaluate a big_Q polynomial (Span<u384>) unreduced.
// q[0] is the constant term; z_powers[i] = z^(i+1) as u384 (BLS12-381 field elements).
pub fn eval_big_Q_u384(q: Span<u384>, z_powers: Span<u384>) -> [felt252; 16] {
    let one = u384 { limb0: 1, limb1: 0, limb2: 0, limb3: 0 };
    let mut acc = unreduced_mul_u384(*q.at(0), one);
    let mut i: usize = 1;
    let len = q.len();
    while i < len {
        acc = add16(acc, unreduced_mul_u384(*q.at(i), *z_powers.at(i - 1)));
        i += 1;
    };
    acc
}

// Reduce check for u288 (BN254).
// Asserts: a(x) == r(x) + q(x) * p_BN254(x) + (2^96 - x) * c(x)  in the Stark field.
// a(x) = sum_{i,j in 0..2} a[3*i+j] * x^(i+j)  (evaluates the outer-product array).
// The identity holds at x = 2^96 by construction: (2^96 - 2^96)*c = 0, confirming a ≡ r mod p.
pub fn reduce_to_u288(a: [felt252; 9], r: [u96; 3], q: [u96; 6], c: [u96; 6], x: felt252) {
    let [a00, a01, a02, a10, a11, a12, a20, a21, a22] = a;
    let x2 = x * x;
    let x3 = x2 * x;
    let x4 = x3 * x;
    let a_val = a00
        + (a01 + a10) * x
        + (a02 + a11 + a20) * x2
        + (a12 + a21) * x3
        + a22 * x4;

    let [r0, r1, r2] = r;
    let r_val: felt252 = r0.into() + r1.into() * x + r2.into() * x2;

    // BN254 prime in base 2^96: limb0 + limb1*x + limb2*x^2
    let p_val: felt252 = 0x6871ca8d3c208c16d87cfd47
        + 0xb85045b68181585d97816a91 * x
        + 0x30644e72e131a029 * x2;

    let [q0, q1, q2, q3, q4, q5] = q;
    let x5 = x4 * x;
    let q_val: felt252 = q0.into()
        + q1.into() * x
        + q2.into() * x2
        + q3.into() * x3
        + q4.into() * x4
        + q5.into() * x5;

    let [c0, c1, c2, c3, c4, c5] = c;
    let c_val: felt252 = c0.into()
        + c1.into() * x
        + c2.into() * x2
        + c3.into() * x3
        + c4.into() * x4
        + c5.into() * x5;

    let b96: felt252 = 0x1000000000000000000000000; // 2^96
    assert(a_val == r_val + q_val * p_val + (b96 - x) * c_val, 'REDUCE_U288_FAILED');
}

// Reduce check for u384 (BLS12-381).
// Asserts: a(x) == r(x) + q(x) * p_BLS12_381(x) + (2^96 - x) * c(x)  in the Stark field.
// a(x) = sum_{i,j in 0..3} a[4*i+j] * x^(i+j).
pub fn reduce_to_u384(a: [felt252; 16], r: [u96; 4], q: [u96; 8], c: [u96; 8], x: felt252) {
    let [a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33] = a;
    let x2 = x * x;
    let x3 = x2 * x;
    let x4 = x3 * x;
    let x5 = x4 * x;
    let x6 = x5 * x;
    let a_val = a00
        + (a01 + a10) * x
        + (a02 + a11 + a20) * x2
        + (a03 + a12 + a21 + a30) * x3
        + (a13 + a22 + a31) * x4
        + (a23 + a32) * x5
        + a33 * x6;

    let [r0, r1, r2, r3] = r;
    let r_val: felt252 = r0.into() + r1.into() * x + r2.into() * x2 + r3.into() * x3;

    // BLS12-381 prime in base 2^96: limb0 + limb1*x + limb2*x^2 + limb3*x^3
    let p_val: felt252 = 0xb153ffffb9feffffffffaaab
        + 0x6730d2a0f6b0f6241eabfffe * x
        + 0x434bacd764774b84f38512bf * x2
        + 0x1a0111ea397fe69a4b1ba7b6 * x3;

    let [q0, q1, q2, q3, q4, q5, q6, q7] = q;
    let x7 = x6 * x;
    let q_val: felt252 = q0.into()
        + q1.into() * x
        + q2.into() * x2
        + q3.into() * x3
        + q4.into() * x4
        + q5.into() * x5
        + q6.into() * x6
        + q7.into() * x7;

    let [c0, c1, c2, c3, c4, c5, c6, c7] = c;
    let c_val: felt252 = c0.into()
        + c1.into() * x
        + c2.into() * x2
        + c3.into() * x3
        + c4.into() * x4
        + c5.into() * x5
        + c6.into() * x6
        + c7.into() * x7;

    let b96: felt252 = 0x1000000000000000000000000; // 2^96
    assert(a_val == r_val + q_val * p_val + (b96 - x) * c_val, 'REDUCE_U384_FAILED');
}
