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

**Theorem 1.2 (Nonzero complementary parameter).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_parameter_ne_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_parameter_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each chart and real 0 < z < 1, the complementary argument 1−parameter(c,z) is nonzero.

**Theorem 1.3 (Analyticity and period-root normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_at_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < z < 1 and any chart and flag, the chosen source is analytic at u = 0. Its value there is 1 for the outgoing flag and the reciprocal of the chosen period root for the inward flag.

**Theorem 1.4 (Square of the chosen source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < z < 1 and any chart and flag, wherever the native factors b(u) and h(e,u,parameter(c,z)) are nonzero, the square of the chosen source is the reciprocal of their product.

**Theorem 1.5 (Native source germ in A and B).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c equal to A or B, require |parameter(c,z)| < 1. For either sign e, the chosen source agrees with sourceMode(e,·,parameter(c,z)) on a neighborhood of the spatial origin.

**Theorem 1.6 (Source normalization on both D lips).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.dLipMean_eq_chosen_chart_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.dLipMean_eq_chosen_chart_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At rD = 1/z with 0 < z < 1, the actual dLipMean equals the chosen D source on the lower radial lip for both signs and on the upper radial lip for the outgoing sign. The upper radial lip reverses the inward source. The identity is pointwise in the spatial coordinate.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_parameter_ne_one`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosenChartSource`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_at_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_square`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.dLipMean_eq_chosen_chart_source`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean](OriginalFourMDLipMean.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance](OriginalFourMSignedCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance](OriginalFourMSlitCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial](../Signed/JSpatial.md)
