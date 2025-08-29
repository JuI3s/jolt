use core::array::from_fn;
use std::str::FromStr;

use ark_bn254::Fr;
use num::BigUint;

use crate::field::JoltField;

// s = 2
pub const FR_THREE_ADICITY: usize = 2;
// t = 2432026985759919469138489527250808343172040488935114927077578242952867610624
pub const FR_TRACE_OF_MODULUS_MINUS_ONE: &[u64] = &[
    243, 202, 698, 575, 991, 946, 913, 848, 952, 725, 080, 834, 317, 204, 048, 893, 511, 492, 707,
    757, 824, 295, 286, 761, 062, 4,
];

// (t - 1) / 3
// 810675661919973156379496509083602781057346829645038309025859414317622536874
pub const FR_TRACE_MINUS_ONE_DIV_BY_THREE: bool = true;
pub const FR_TRACE_PLUS_OR_MINUS_ONE_DIV_THREE: &[u64] = &[
    810, 675, 661, 919, 973, 156, 379, 496, 509, 083, 602, 781, 057, 346, 829, 645, 038, 309, 025,
    859, 414, 317, 622, 536, 874,
];

pub enum CbrtPrecomputation<F: JoltField> {
    TonelliShanks {
        three_adicity: u32,
        cubic_nonresidue_to_trace: F,
        trace_of_modulus_minus_one: &'static [u64],
        trace_plus_or_minus_one_div_three: &'static [u64],
        trace_minus_one_div_by_three: bool,
    },
}

fn to_le_limb_first(arr: &[u64]) -> Vec<u64> {
    arr.iter().rev().copied().collect::<Vec<_>>()
}

// Compute the cube root of a cube in Fr using Tonelli-Shanks.
/// p4 section 3.1 from https://eprint.iacr.org/2009/457.pdf
pub fn cube_root_tonelli_shanks<F: ark_ff::Field>(
    a: F,
    three_adicity: u32,
    cubic_nonresidue_to_trace: &F,
    trace_of_modulus_minus_one: &[u64],
    trace_plus_or_minus_one_div_three: &[u64],
    trace_minus_one_div_by_three: bool,
) -> F {
    // Step 1 is preprocessing

    // Step 2
    let mut c = cubic_nonresidue_to_trace.inverse().unwrap();
    let mut r = a.pow(trace_of_modulus_minus_one);

    // Step 3 Computation of the cube root of (a^t)^-1
    let mut h = F::one();
    let exp = [3_u64.pow(three_adicity - 1)];

    let c_prime = c.pow(&exp);

    for i in 1..three_adicity {
        // TODO: check this to_digit()
        let exp = [3_u64.pow(three_adicity - i - 1)];

        let d = r.pow(exp);
        if d == c_prime {
            h *= c;
            r *= c.square() * c;
        } else if d != F::one() {
            // The condition is equivalent to d = c_prime^2
            h *= c.square();
            r *= (c.square() * c).square();
        }
        c *= c.square();
    }

    // Step 4
    let r = a.pow(trace_plus_or_minus_one_div_three) * h;
    if trace_minus_one_div_by_three {
        r.inverse().unwrap()
    } else {
        r
    }
}

pub fn sqrt<F: ark_ff::Field>(
    elem: &F,
    two_adicity: &usize,
    quadratic_nonresidue_to_trace: &F,
    trace_of_modulus_minus_one_div_two: &[u64],
) -> Option<F> {
    // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
    // Actually this is just normal Tonelli-Shanks; since `P::Generator`
    // is a quadratic non-residue, `P::ROOT_OF_UNITY = P::GENERATOR ^ t`
    // is also a quadratic non-residue (since `t` is odd).
    if elem.is_zero() {
        return Some(F::zero());
    }
    // Try computing the square root (x at the end of the algorithm)
    // Check at the end of the algorithm if x was a square root
    // Begin Tonelli-Shanks
    let mut z = *quadratic_nonresidue_to_trace;
    let mut w = elem.pow(trace_of_modulus_minus_one_div_two);
    let mut x = w * elem;
    let mut b = x * &w;

    let mut v = *two_adicity as usize;

    while !b.is_one() {
        let mut k = 0usize;

        let mut b2k = b;
        while !b2k.is_one() {
            // invariant: b2k = b^(2^k) after entering this loop
            b2k.square_in_place();
            k += 1;
        }

        if k == (*two_adicity as usize) {
            // We are in the case where self^(T * 2^k) = x^(P::MODULUS - 1) = 1,
            // which means that no square root exists.
            return None;
        }
        let j = v - k;
        w = z;
        for _ in 1..j {
            w.square_in_place();
        }

        z = w.square();
        b *= &z;
        x *= &w;
        v = k;
    }
    // Is x the square root? If so, return it.
    if x.square() == *elem {
        Some(x)
    } else {
        // Consistency check that if no square root is found,
        // it is because none exists.
        debug_assert!(!matches!(elem.legendre(), ark_ff::LegendreSymbol::QuadraticResidue));
        None
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use ark_bn254::Fr;
    use ark_ff::Field;
    use num::BigUint;

    use super::*;

    fn find_cubic_nonresidue<F: Field>(char_minus_1_div_three: &[u64]) -> F {
        let mut x = F::from(2_u64);
        loop {
            // if x^(p-1)/3 is not 1, then x is a cubic non-residue
            if x.pow(char_minus_1_div_three) != F::one() {
                break;
            }
            x += F::from(1_u64);
        }
        x
    }

    fn find_quadratic_nonresidue<F: Field>(char_minus_1_div_two: &[u64]) -> F {
        let mut x = F::from(2_u64);
        loop {
            if x.pow(char_minus_1_div_two) != F::one() {
                break;
            }
    }

    #[test]
    fn test_impl_flatten_u64_arr_to_digits() {
        let arr = [2, 0];
        let mut a = Fr::from(2_u64);

        let b = a.pow(&arr);
        a.square_in_place();
        assert_eq!(b, a);
    }

    #[test]
    fn test_cube_root_finding() {
        // (21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1) // 3

        let char_minus_1_div_three = BigUint::from_str(
            "7296080957279758407415468581752425029516121466805344781232734728858602831872",
        )
        .unwrap()
        .to_u64_digits();

        // Should be 3
        let nonresidue = find_cubic_nonresidue::<Fr>(&char_minus_1_div_three);
        let nonresidue_to_trace = nonresidue.pow(&FR_TRACE_OF_MODULUS_MINUS_ONE);

        let mut cube = Fr::from(5_u64);
        cube = cube * cube * cube;

        let mut cbrt = cube_root_tonelli_shanks(
            cube,
            FR_THREE_ADICITY as u32,
            &nonresidue_to_trace,
            &to_le_limb_first(FR_TRACE_OF_MODULUS_MINUS_ONE),
            &to_le_limb_first(FR_TRACE_PLUS_OR_MINUS_ONE_DIV_THREE),
            FR_TRACE_MINUS_ONE_DIV_BY_THREE,
        );
        cbrt = cbrt * cbrt * cbrt;

        assert_eq!(cube, cbrt);
    }

    fn test_sqrt_finding() {


        todo!()
    }
}
