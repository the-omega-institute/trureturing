# Independent native mode assignments

## Abstract

Fixed-charge Wick transport at the four punctures

**Theorem 1.1 (Fixed-charge marked coefficient as a Wick assignment sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick.physical_marked_coefficient_assign`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick.physical_marked_coefficient_assign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lattice with unit Gram determinant and a word of distinct labels from a finite type, fix the charge, the puncture, colour and spatial degree at each occurrence, and a real chart argument strictly between zero and one. In A or B require the slit parameter to have norm less than one. In D use the true lip. The physical marked Taylor coefficient is the charge exponential times the ordered partition sum. The correction endpoints carry the signed scales and four within-puncture contraction factors. Every surviving occurrence independently selects a native mode through its requested degree, with the signed inverse jet weight and the native covariance and mean entries.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick.physical_marked_coefficient_assign`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries](OriginalFourMNativeWickEntries.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering](OriginalFourMSlotCorrectionLowering.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments](../Wick/AffineWickAssignments.md)
