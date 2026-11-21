# The A and B germs and both D lips

## Abstract

Native signed sources on the four-point charts

For 0 < z < 1, the chart parameters are rA = 1−1/z, rB = z and rD = 1/z. The choice upperA = true selects the lower D lip Im r < 0. The choice upperA = false selects the upper D lip Im r > 0.

**Definition 1.1 (Source with the chosen period root).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosenChartSource`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosenChartSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write r for the chart parameter, b = b(u) and h = h(e,u,r). The outgoing source is (h/b)^(−1/2)/b. The inward source is (h/[b(1−r)])^(−1/2)/(b periodRoot(c,z)). The chosen D root is the lower radial lip at rD.

**Theorem 1.2 (Native source germ in A and B).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c equal to A or B, require |parameter(c,z)| < 1. For either sign e, the chosen source agrees with sourceMode(e,·,parameter(c,z)) on a neighborhood of the spatial origin.

**Theorem 1.3 (Source normalization on both D lips).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.dLipMean_eq_chosen_chart_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.dLipMean_eq_chosen_chart_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At rD = 1/z with 0 < z < 1, the actual dLipMean equals the chosen D source on the lower radial lip for both signs and on the upper radial lip for the outgoing sign. The upper radial lip reverses the inward source. The identity is pointwise in the spatial coordinate.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosenChartSource`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.dLipMean_eq_chosen_chart_source`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean](OriginalFourMDLipMean.md)
