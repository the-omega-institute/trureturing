# Separation of algebraic phase products

## Abstract

A field norm gives a separation bound after clearing denominators in a signed phase product.

**Theorem 1.1 (Separation at every complex embedding).**

Lean statement: `D5/S3/Fourier/Asymptotics/AlgebraicPhaseSeparation.signed_product_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/AlgebraicPhaseSeparation.signed_product_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a number field of degree d. Take finitely many phases in K whose images under every complex embedding have modulus one. Suppose multiplication by a common positive integer D makes each phase and its inverse integral over the integers. Form the product w of the phases to arbitrary integer exponents and let B be D raised to the sum of the absolute exponents. If w differs from one, then every complex embedding σ satisfies 1 ≤ |σ(w) − 1| B (2B)^(d−1).

Choose the phase or its inverse according to the sign of each exponent. Multiplying the corresponding powers of the cleared factors gives the algebraic integer Bw. Then B(w−1) is a nonzero algebraic integer. Its absolute field norm is at least one, and each conjugate has modulus at most 2B. Retain the modulus at σ separately in the norm estimate.

The bound applies to the algebraic products underlying two-clock Fourier modes once multiplicative independence and the denominator premises have been established for those phases.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/AlgebraicPhaseSeparation.signed_product_separation`
