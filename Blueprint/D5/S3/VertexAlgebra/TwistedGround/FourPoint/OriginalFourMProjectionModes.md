# Signed Mode Projection

## Abstract

Literal four-point occupation selectors on the signed mode diagonals

**Theorem 1.1 (Left lowering coefficients on the actual diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.project_occupations_on_signed_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.project_occupations_on_signed_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original two selectors evaluate to one on the supported occupations, leaving the finite negative-lowering coefficients and the original overall parity phase.

**Theorem 1.2 (Detector displacement for arbitrary signed modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.detector_selector_on_signed_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.detector_selector_on_signed_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lowering the detector by ell shifts the signed diagonal by ell, directly in the original output selector.

**Theorem 1.3 (The original compact occupation inside the common mode box).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.bounded_external_sewn_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.bounded_external_sewn_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedding preserves the native affine coefficient and all four occupation factorials in the original sewn charge term.

**Theorem 1.4 (Native normalization of the real overlap coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.physical_chart_coefficient_overlap_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.physical_chart_coefficient_overlap_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-24 sector identity uses the inverse sixth power of the common real coordinate to normalize the B coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.bounded_external_sewn_charge`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.detector_selector_on_signed_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.physical_chart_coefficient_overlap_normalized`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.project_occupations_on_signed_diagonal`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport](../../HalfFock/OriginalHalfCurrentTransport.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm](OriginalFourMChargeGerm.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick](OriginalFourMSpatialWick.md)
