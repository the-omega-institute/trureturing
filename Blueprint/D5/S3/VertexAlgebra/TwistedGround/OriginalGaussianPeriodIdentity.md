# Original Gaussian Determinant Period Identity

## Abstract

Original Gaussian Determinant Period Identity

The original finite logarithms vanish at the zero operator, fixing the infinite logarithm and determinant constants at zero. Equality of radial logarithmic derivatives is integrated on the interior and extended continuously to zero. The principal complex logarithm is legal throughout the disk because the real part of one minus z squared is positive. The analytic identity principle extends the real formula to the whole complex unit disk. Nonvanishing of the existing period follows from that identity and the original exponential determinant, with no nonvanishing premise.

These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.

**Theorem 1.1 (gaussianLogDet_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original infinite-cycle logarithm is zero at the zero operator, by the actual finite cutoff limit.

**Theorem 1.2 (gaussianDet_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original exponential determinant equals one at zero.

**Theorem 1.3 (gaussianLogDet_real_normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_real_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_real_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with zero less than or equal to r and r less than one, the original logarithm at sqrt r equals the real logarithm of F r plus one quarter of the real logarithm of one minus r.

**Theorem 1.4 (gaussianDet_real_period_identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_real_period_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_real_period_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r from zero inclusive to one exclusive, the original determinant at sqrt r equals one minus r to the real power one quarter, multiplied by the existing F r, embedded into the complex numbers.

**Theorem 1.5 (gaussianDet_complex_period_identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z of norm less than one, the original determinant equals exp of one quarter times the principal log of one minus z squared, multiplied by the existing OriginalHalfBinomialPeriod.period at z squared.

**Theorem 1.6 (period_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.period_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.period_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing OriginalHalfBinomialPeriod.period is nonzero at every complex argument of norm less than one.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_real_period_identity`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_real_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.period_ne_zero`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant](OriginalGaussianDeterminant.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear](OriginalGaussianTraceBilinear.md)
