use std::str::FromStr;

use num::{BigUint, One};

use crate::{field::JoltField, utils};

fn modulus() -> BigUint {
    BigUint::from_str(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    )
    .unwrap()
}

fn generator() -> BigUint {
    BigUint::from_str("5").unwrap()
}

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

fn compute_two_adic_trace(modulus: &BigUint) -> (BigUint, usize) {
    // modulus - 1 = 2^s * t
    let mut trace = modulus - BigUint::from_str("1").unwrap();
    let mut s = 0;
    while !trace.bit(0) {
        trace >>= 1u8;
        s += 1;
    }
    (trace, s)
}

fn compute_three_adic_trace(modulus: &BigUint) -> (BigUint, usize) {
    let mut trace = modulus - BigUint::from_str("1").unwrap();
    let mut s = 0;
    let three = BigUint::from_str("3").unwrap();
    let zero = BigUint::from_str("0").unwrap();
    while &trace % &three == zero {
        trace /= &three;
        s += 1;
    }
    (trace, s)
}

fn three_adic_trace_plus_or_minus_one_div_three(trace: &BigUint) -> (BigUint, bool) {
    let three = BigUint::from_str("3").unwrap();
    let one = BigUint::from_str("1").unwrap();

    assert_ne!(trace % &three, BigUint::from_str("0").unwrap());

    if trace % &three == one {
        ((trace - &one) / three, true)
    } else {
        ((trace + &one) / three, false)
    }
}

fn compute_adic_root_of_unity(trace: &BigUint, generator: &BigUint, modulus: &BigUint) -> BigUint {
    generator.modpow(&trace, modulus)
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
    let mut c = cubic_nonresidue_to_trace.clone();
    let mut r = a.pow(trace_of_modulus_minus_one);

    // Step 3 Computation of the cube root of (a^t)^-1
    let mut h = F::one();
    let exp = [3_u64.pow(three_adicity - 1)];

    let c_prime = c.pow(&exp);
    c = c.inverse().unwrap();

    for i in 1..three_adicity {
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
        debug_assert!(!matches!(
            elem.legendre(),
            ark_ff::LegendreSymbol::QuadraticResidue
        ));
        None
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use ark_bn254::Fr;
    use ark_ff::Field;
    use ark_std::test_rng;
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
    #[test]
    fn test_impl_flatten_u64_arr_to_digits() {
        let arr = [2, 0];
        let mut a = Fr::from(2_u64);

        let b = a.pow(&arr);
        a.square_in_place();
        assert_eq!(b, a);
    }

    #[test]
    fn test_sqrt_finding() {
        // This is the artworks sqrt implementation.
        let modulus = modulus();
        let generator = generator();
        let (trace, two_adicity) = compute_two_adic_trace(&modulus);
        let two_adic_root_of_unity =
            compute_adic_root_of_unity(&trace, &generator, &modulus).to_string();
        let two_adic_root_of_unity = Fr::from_str(&two_adic_root_of_unity).unwrap();

        // test two adic root of unity is not a quadratic residue
        let modulus_minus_one_div_two = (modulus - BigUint::from(1_u64)) / BigUint::from(2_u64);
        assert_ne!(
            two_adic_root_of_unity.pow(modulus_minus_one_div_two.to_u64_digits()),
            Fr::one()
        );

        let mut square = Fr::from(2_u64);
        square = square * square;
        let sqrt = sqrt(
            &square,
            &two_adicity,
            &two_adic_root_of_unity,
            &(trace / BigUint::from(2_u64)).to_u64_digits(),
        )
        .unwrap();
        assert_eq!(square, sqrt * sqrt);
    }

    #[test]
    fn test_cube_root_finding() {
        let modulus = modulus();
        let generator = generator();
        let (trace, three_adicity) = compute_three_adic_trace(&modulus);
        assert_eq!(three_adicity, 2);

        let three_adic_root_of_unity =
            compute_adic_root_of_unity(&trace, &generator, &modulus).to_string();
        let three_adic_root_of_unity = Fr::from_str(&three_adic_root_of_unity).unwrap();

        assert_eq!(
            Fr::from(generator.clone()).pow(trace.to_u64_digits()),
            three_adic_root_of_unity
        );
        {
            let modulus_minus_one_div_three =
                (modulus - BigUint::from(1_u64)) / BigUint::from(3_u64);
            assert_ne!(
                Fr::from(generator.clone()).pow(modulus_minus_one_div_three.to_u64_digits()),
                Fr::one()
            );
        }

        let (trace_plus_or_minus_one_div_three, trace_minus_one_div_by_three) =
            three_adic_trace_plus_or_minus_one_div_three(&trace);

        let mut rng = test_rng();
        let num_tests = 5;
        for _ in 0..num_tests {
            let mut cube = Fr::random(&mut rng);
            cube = cube * cube * cube;

            let cbrt = cube_root_tonelli_shanks(
                cube,
                three_adicity as u32,
                &three_adic_root_of_unity,
                &trace.to_u64_digits(),
                &trace_plus_or_minus_one_div_three.to_u64_digits(),
                trace_minus_one_div_by_three,
            );

            assert_eq!(cube, cbrt * cbrt * cbrt);
        }
    }
}
