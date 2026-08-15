# Gaussian Integer Norm

## Abstract

A Gaussian integer times its complex conjugate is its sum-of-two-squares norm.

**Theorem 1.1 (The conjugate product is the sum-of-two-squares norm).**

$$\forall a, b\in\mathbb{Z},\ (a+bi)(a-bi) = a^2+b^2$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/GaussianIntegers/GaussianIntegerNorm.gaussian_integer_mul_conj_eq_sq_add_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all integers a and b, embed the Gaussian integer a + bi into the complex numbers. Its product with a - bi, the complex conjugate, is the embedded integer a squared plus b squared.

Pinned Mathlib supplies Complex.mul_conj and Complex.normSq_apply, so the Lean proof is a thin wrapper around the standard complex norm identity. No claim is made here about constructing the Gaussian integer quotient or the surrounding number-system completion chain.

## References

- Truth anchor: `D5/S3/PrimeForms/GaussianIntegers/GaussianIntegerNorm.gaussian_integer_mul_conj_eq_sq_add_sq`
