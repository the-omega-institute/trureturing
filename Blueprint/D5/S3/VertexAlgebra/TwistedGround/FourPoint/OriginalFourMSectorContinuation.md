# Holomorphic fixed-occupation charge sectors on the Euler slit

## Abstract

Normal convergence and native agreement of the rank-24 charge-sector terms

**Theorem 1.1 (Holomorphy of a fixed-occupation coset sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the real Gram matrix be positive definite and fix four occupations and a mod-two charge class. On an open chart, assume the scalar prefactor, nome, covariance entries and signed mean factors are complex differentiable, with the nome strictly subunit. The actual coset sum is complex differentiable there. Around each point, a closed subball gives a summable majorant for the full charge family. Restriction to the chosen coset preserves that bound, and the finite occupation polynomial makes the individual terms holomorphic. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.compact_charge_normal`

**Definition 1.2 (Continued term at a fixed charge).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the square parameter r, multiply the rank-24 determinant by the slit nome to the natural charge energy and by the affine coefficient for the specified occupation. The two tagged copies of the finite support give its matrix and linear indices. The linear factor at each index is its slit mean entry times the charge pairing. `D5/S3/Analytic/OriginalSlitNome.rank24Determinant`, `D5/S3/Analytic/OriginalSlitNome.slitNome`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry`

**Definition 1.3 (Slit charge-sector sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the continued terms over charges in the selected mod-two class, with zero contribution from all other charges.

**Theorem 1.4 (Holomorphy throughout the Euler slit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive definite real Gram matrix and each fixed occupation and charge class, the slit sector sum is complex differentiable throughout the Euler slit. The determinant and the Taylor entries give the chart data, and the subunit nome gives a uniform strict bound on every compact subball. `D5/S3/Analytic/OriginalSlitNome.slitNome_norm_lt_one`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_analyticOnNhd`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_analyticOnNhd`

**Theorem 1.5 (Exact agreement with native sewing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite rank-24 lattice datum, any fixed occupations and any individual charge, the continued term at r = w² equals the original sewn term for every complex |w| < 1. The exact Taylor entries identify the native covariance and mean. The determinant uses the twelfth power of the Gaussian period identity, and the disk nome recovers the native displacement exponential, both charge scalars and the power of w. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.sewnChargeTerm`, `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity`, `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_Q0`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_eq_native`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_eq_native`

## References

- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.rank24Determinant`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_Q0`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_norm_lt_one`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.compact_charge_normal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.sewnChargeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitCovarianceEntry_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.slitMeanEntry_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity`
- Dependency: [D5/S3/Analytic/OriginalSlitNome](../../../Analytic/OriginalSlitNome.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal](OriginalFourMChargeNormal.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor](OriginalFourMSlitTaylor.md)
