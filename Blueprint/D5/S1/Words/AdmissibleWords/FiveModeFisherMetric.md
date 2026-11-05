# The five-mode Fisher Riemannian metric

## Abstract

The actual four-dimensional affine chart of positive five-mode laws carries a smooth Fisher metric on its tangent bundle.

Coordinates are functions from Fin 4 to the reals. simplexDomain is the open subset chartDomain from FiveModeFisherImmersion, and FiveModeManifold is its subtype. The smooth structure is the one inherited from that open subset of the real normed space.

**Definition 1.1 (The continuous bilinear form in chart coordinates).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherMetricForm`

*Formalization.* `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherMetricForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each q the form is the sum over s in Fin 5 of the inverse probability simplexLaw(q)(s) times the product of the two s-coordinate projections of tangentLift. Its value on u and v is exactly fisher(simplexLaw(q),tangentLift(u),tangentLift(v)).

**Definition 1.2 (A smooth metric on the actual tangent bundle).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherRiemannianMetric`

*Formalization.* `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherRiemannianMetric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fisherRiemannianMetric is a Bundle.ContMDiffRiemannianMetric with smoothness order infinity and model space Fin 4 to the reals, on TangentSpace at each point of FiveModeManifold. Its inner form is fisherMetricForm. Symmetry follows from commutation of the two tangent factors; strict positivity is supplied by the square-root immersion.

For a positive normalized law, each probability is at most one. A metric unit ball therefore bounds each coordinate of a tangent vector by one, giving the required boundedness property. Smoothness follows from smooth affine probabilities and inversion on their positive domain, with the open-subset tangent trivializations identified explicitly.

The associated fisherRiemannianBundle instance supplies the Riemannian bundle structure. Lean synthesizes both IsContMDiffRiemannianBundle at order infinity and IsContinuousRiemannianBundle. This construction establishes a probability-manifold metric; it does not assert geodesic completeness, curvature bounds or a relation between its spectrum and the Riemann hypothesis.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherMetricForm`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherRiemannianMetric`
- Dependency: [D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion](FiveModeFisherImmersion.md)
