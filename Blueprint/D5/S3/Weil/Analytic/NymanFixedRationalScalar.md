# The fixed rational scalar forces the Riemann hypothesis

## Abstract

The fixed rational scalar forces the Riemann hypothesis

**Definition 1.1 (The finite rational shell sum).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalScalar.scalar`

*Formalization.* `D5/S3/Weil/Analytic/NymanFixedRationalScalar.scalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar at N is the sum of μ(n)bRat(n/N) over N < n ≤ 2N, with the weights and the sum evaluated over the rationals.

**Definition 1.2 (Square-root growth with arbitrary positive slack).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalScalar.ScalarSquareRoot`

*Formalization.* `D5/S3/Weil/Analytic/NymanFixedRationalScalar.ScalarSquareRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each ε > 0 there is a nonnegative constant C such that the absolute value of the scalar is at most C N^(1/2+ε) for every positive natural N.

**Theorem 1.3 (The bound implies the Riemann hypothesis).**

Lean statement: `D5/S3/Weil/Analytic/NymanFixedRationalScalar.rh_of_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanFixedRationalScalar.rh_of_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite rational sums agree with the real-scale test at t = 1/N. The Lipschitz estimate transfers growth from these samples to all small positive t. A zeta zero in the right half-strip would force a zero of the explicit Mellin product, which is nonvanishing there. Right-half-strip reduction gives the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalScalar.ScalarSquareRoot`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalScalar.rh_of_scalar`
- Truth anchor: `D5/S3/Weil/Analytic/NymanFixedRationalScalar.scalar`
- Dependency: [D5/S3/Weil/Analytic/NymanFixedRationalKernelLipschitz](NymanFixedRationalKernelLipschitz.md)
- Dependency: [D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin](NymanFixedRationalKernelMellin.md)
- Dependency: [D5/S3/Weil/Analytic/NymanShellScale](NymanShellScale.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
