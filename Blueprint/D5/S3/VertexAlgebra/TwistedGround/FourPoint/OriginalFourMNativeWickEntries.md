# Signed covariance and charge-linear mean

## Abstract

Native Wick entries at the four punctures

**Theorem 1.1 (Covariance in the A and B charts).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.nativeTaylor_ab`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.nativeTaylor_ab` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an interior real chart argument, when the A or B slit parameter has norm less than one, each physical native covariance Taylor entry is the double inverse jet sum of the signed slit covariance entries, with a relative sign factor from each puncture.

**Theorem 1.2 (Covariance on the D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.nativeTaylor_d`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.nativeTaylor_d` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an interior real argument on the actual D lip, the covariance is the corresponding double inverse jet sum of the literal D lip entries, with the two D relative factors.

**Theorem 1.3 (Charge-linear mean in the A and B charts).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.meanTaylor_ab`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.meanTaylor_ab` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any fixed charge, under the A or B interior and slit-parameter hypotheses, the physical singleton equals the inverse jet sum of slit mean entries times the charge bilinear and the relative factor of that puncture.

**Theorem 1.4 (Charge-linear mean on the D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.meanTaylor_d`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.meanTaylor_d` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an interior argument on the actual D lip, the fixed-charge singleton equals the corresponding inverse jet sum of the literal D lip means times the charge bilinear and D relative factor.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.meanTaylor_ab`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.meanTaylor_d`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.nativeTaylor_ab`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.nativeTaylor_d`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMBivariateInverseJets](OriginalFourMBivariateInverseJets.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent](OriginalFourMDFourCurrent.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition](OriginalFourMSpatialWickPartition.md)
