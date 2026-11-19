# Spatial Taylor Selection

## Abstract

Spatial Taylor selection of the original simultaneous marked Gaussian

**Theorem 1.1 (Spatial coefficients through the marked Wick recurrence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.spatial_marked_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.spatial_marked_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the recursion the selected occurrence belongs to either a singleton or a pair. Its spatial Taylor coefficient acts on that factor, leaving the remaining coordinate selections to the remaining marks.

**Theorem 1.2 (A native occupation after the simultaneous spatial Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_occupation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_occupation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed charge on radial A or B, the simultaneous coefficient of the physical Gaussian gives the literal native affine occupation after the four inverse-lowered words.

**Theorem 1.3 (Marked charge summands of the actual physical product).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_product_marked_charge_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_product_marked_charge_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the actual charge fiber of each physical chart, the relative source signs multiply each occurrence weight and the original period factor multiplies the full sum.

**Theorem 1.4 (Original sewn readout of a marked charge summand).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_sewn_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_sewn_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the native radial nome, the readout includes the original determinant, charge energy and scalar. The period normalization adds the cube of the complementary parameter.

**Theorem 1.5 (Sector identities of the simultaneous marked Taylor coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under joint analyticity at the marked origin, Taylor extraction preserves the actual Fourier and quadratic sector identities and the original B-chart period multiplier.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_product_marked_charge_fiber`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_occupation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.radial_spatial_sewn_charge`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.spatial_marked_gaussian`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMJointWick](OriginalFourMJointWick.md)
