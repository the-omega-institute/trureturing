# Holomorphic boundary entries and agreement on the open lip

## Abstract

Taylor entries of the native D-lip mean and covariance and their slit agreement

**Definition 1.1 (D-lip mean entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the signed mean on the selected D lip, multiply by minus the leg sign and divide by the D period before taking the ordinary external coefficient of order p. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean`

**Theorem 1.2 (Holomorphic D-lip mean entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either lip, every leg, sign and Taylor order gives an analytic function at each real t > 1 viewed in ℂ. The source is jointly holomorphic and the D period is nonzero at t, so taking the fixed external coefficient preserves analyticity. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_joint_analytic`

**Theorem 1.3 (Mean entry agreement on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every point on the selected open D lip, equality of the source germs near the external origin and equality of the periods identify the two mean entries. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_eventuallyEq`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry`

**Definition 1.4 (D-lip covariance entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the selected D-lip covariance by the complex Gram entry of the labels and take ordinary Taylor coefficients at zero in u and v using their mode orders. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance`

**Theorem 1.5 (Holomorphic D-lip covariance entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t > 1 the D-lip covariance is jointly holomorphic at (0,0,t). Two successive applications of the analytic slice argument give boundary analyticity of the fixed entry for either lip and every pair of signed labels. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_joint_analytic`

**Theorem 1.6 (Covariance entry agreement on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix r on the selected open D lip. Mean agreement holds near each external origin, so covariance agreement holds near both origins. Germ congruence for each Taylor extraction identifies the full entry, including the Gram factor. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_eq_of_means`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry`

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_eq_of_means`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_eventuallyEq`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance](OriginalFourMDLipCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance](OriginalFourMSignedCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor](OriginalFourMSlitTaylor.md)
