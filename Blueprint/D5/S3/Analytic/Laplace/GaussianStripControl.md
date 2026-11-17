# Gaussian strip control

## Abstract

Holomorphy and quadratic growth on the strip used for Gaussian Laplace inversion.

**Definition 1.1 (A wider strip for the regular term).**

Lean statement: `D5/S3/Analytic/Laplace/GaussianStripControl.GaussianStripControl`

*Formalization.* `D5/S3/Analytic/Laplace/GaussianStripControl.GaussianStripControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complex function J has Gaussian strip control if it is holomorphic where -1/5 < Re(s) < 1 and there is a nonnegative constant C such that its norm is at most C times (1 + abs(Im(s))) squared throughout the closed strip -1/6 <= Re(s) <= 3/4. The constant is independent of both coordinates of s.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/GaussianStripControl.GaussianStripControl`
- Dependency: [D5/S3/Analytic/Laplace/PairedPoleRegularity](PairedPoleRegularity.md)
