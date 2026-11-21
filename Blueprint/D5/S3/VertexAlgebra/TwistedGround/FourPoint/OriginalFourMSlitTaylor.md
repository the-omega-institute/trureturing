# Signed mean and covariance coefficients

## Abstract

Exact Taylor entries of the native signed Gaussian on the Euler slit

**Theorem 1.1 (Analytic dependence of a Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.analytic_coefficient_slice`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.analytic_coefficient_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be complex analytic at (0,y) on the product of ℂ and a complex normed space. For every n, the ordinary order-n coefficient at zero of the first variable is analytic in the remaining variable at y. Iterate the directional Fréchet derivative in the first coordinate, restrict to the slice at zero and divide by n factorial. Near y those directional derivatives agree with the iterated one-variable derivatives.

**Theorem 1.2 (Taylor coefficients of equal germs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.coefficient_congr`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.coefficient_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two complex functions agree near zero, then their iterated derivatives at zero agree. Dividing by the same factorial gives equal coefficients.

**Definition 1.3 (Slit mean entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a fixed leg and sign, take the ordinary coefficient of order p at the external origin of the slit mean multiplied by minus the leg sign and divided by the Euler period. The lattice pairing with the charge supplies the remaining linear factor. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean`

**Theorem 1.4 (Holomorphic mean entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fixed Taylor entry of the signed mean is holomorphic in r on the Euler slit. Iterate the Fréchet derivative in the external coordinate, restrict to the external origin, and divide by p factorial. This agrees locally with the one-variable derivative. The joint germ is supplied by `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_joint_analytic`.

**Definition 1.5 (Slit covariance entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the signed covariance germ by the complex Gram entry of the two labels. Take the ordinary Taylor coefficient in each external variable at zero, using their respective mode orders. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance`

**Theorem 1.6 (Holomorphic covariance entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all leg choices and signed external labels the iterated coefficient is holomorphic in r on the Euler slit. Apply the analytic slice argument first to u with (v,r) as parameters and then to v with r as parameter. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_joint_analytic`

**Theorem 1.7 (Identification with the original covariance entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex opening w with |w| < 1, the slit coefficient at r = w² equals the actual effective kernel at the two tagged modes. The covariance germs agree on small external disks, hence their successive derivatives at zero agree. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_tagged_entry`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_eq_native`

**Theorem 1.8 (Identification with the original charge-linear entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each charge and tagged mode at |w| < 1, pairing the charge with the label's unit charge and multiplying by the slit entry at w² gives the actual Gaussian mean. The native source-amplitude series converges around the external origin. Coefficient extraction recovers its p-th amplitude with the period and leg factors. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_eq_sourceMode`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean`

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_mean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance.native_tagged_entry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_eq_sourceMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.analytic_coefficient_slice`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.coefficient_congr`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_eq_native`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance](OriginalFourMSlitCovariance.md)
