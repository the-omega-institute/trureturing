# Analyticity at the D boundary and equality with the slit sector

## Abstract

Analytic continuation of the original fixed-occupation D-lip charge-sector sum

**Definition 1.1 (Fixed-occupation charge-sector sum on the D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the selected lip and charge class, form the affine coefficient from the signed D-lip Taylor entries and charge pairings. Each term carries the D nome to the natural charge energy and the factor (1 − r)⁻³ times the D period to power −12. The sum keeps precisely the selected mod-two charge class. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry`

**Theorem 1.2 (Analytic continuation at every real t > 1).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite real Gram matrix, either lip and every fixed occupation and charge class, the charge-sector sum is analytic at t viewed in ℂ. Finiteness of the tagged support gives a common neighborhood where all mean and covariance entries are holomorphic. The determinant is holomorphic there after restricting the neighborhood, and the D nome stays strictly subunit. Apply the open-chart coset convergence theorem on a ball in that neighborhood. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_subunit_near`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn`

**Theorem 1.3 (Termwise agreement on the selected open D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every point of the chosen open lip, the two sector sums agree for all occupations and charge classes. The point lies on the double slit, so equality of the period-ratio exponentials gives nome agreement. The D period and both Taylor entries also take their slit values, giving equality at every charge. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_eq_exp`, `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_exp`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_eq_slit`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_eq_slit`

## References

- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_exp`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_eq_exp`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_subunit_near`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSector.dLipChargeSector_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipCovarianceEntry_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor.dLipMeanEntry_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome](OriginalFourMDLipNome.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTaylor](OriginalFourMDLipTaylor.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation](OriginalFourMSectorContinuation.md)
