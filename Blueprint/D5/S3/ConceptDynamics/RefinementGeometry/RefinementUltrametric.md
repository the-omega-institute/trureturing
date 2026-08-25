# Refinement Ultrametric

## Abstract

Agreement depth gives a pseudoultrametric; an ultrametric under separation.

**Theorem 1.1 (Refinement distance satisfies the strong triangle inequality).**

$$\operatorname{refinementDistance}\left(Coordinate, readout, horizon, x, z\right) \leq \operatorname{max}\left(\operatorname{refinementDistance}\left(Coordinate, readout, horizon, x, y\right), \operatorname{refinementDistance}\left(Coordinate, readout, horizon, y, z\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/RefinementUltrametric.refinementDistance_ultrametric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distance uses common agreement depth and a finite horizon. The strong triangle inequality holds without state separation.

Agreement through the smaller common depth composes transitively and yields the maximum bound.

**Theorem 1.2 (Horizon separation turns the pseudodistance into a metric).**

$$\operatorname{SeparatesByHorizon}\left(Coordinate, readout, horizon\right) \Rightarrow (\operatorname{refinementDistance}\left(Coordinate, readout, horizon, x, y\right) = zero \iff x = y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/RefinementUltrametric.refinementDistance_eq_zero_iff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit SeparatesByHorizon hypothesis supplies identity of indiscernibles.

The construction is unconditionally a pseudoultrametric and becomes an ultrametric only under horizon separation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/RefinementUltrametric.refinementDistance_eq_zero_iff_eq`
- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/RefinementUltrametric.refinementDistance_ultrametric`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
