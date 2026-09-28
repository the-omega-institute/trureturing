# Multiplier Root-Polynomial Selection

## Abstract

Multiplier invariance restricts the degrees present in a finite root polynomial.

**Theorem 1.1 (Nonresonant root-polynomial coefficients vanish).**

Lean statement: `D5/S3/ArithUnits/MultiplierRootPolynomialSelection.coeff_zero_of_mul_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MultiplierRootPolynomialSelection.coeff_zero_of_mul_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite subset of a field invariant under a nonzero multiplier, a coefficient of its monic root polynomial vanishes when the multiplier acts nontrivially on the corresponding elementary symmetric function. The proof uses the multiplier permutation, Mathlib's symmetric scaling identity, and Vieta's formula. It does not require characteristic zero.

## References

- Truth anchor: `D5/S3/ArithUnits/MultiplierRootPolynomialSelection.coeff_zero_of_mul_invariant`
