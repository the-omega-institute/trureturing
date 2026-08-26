# Cycle Collapse Projection

## Abstract

Cyclic realization paths collapse to one logical node under an antisymmetric monotone projection.

**Theorem 1.1 (Mutual realization paths collapse in a partial order).**

$$\begin{gathered}\forall realEdge: Real \to Real \to Prop, projection: Real \to Logical, first, second: Real,\\{}[\operatorname{PartialOrder}\left(Logical\right)],\\{}(\operatorname{EdgeMonotoneProjection}\left(realEdge, le, projection\right) \land \operatorname{ReflTransGen}\left(realEdge, first, second\right) \land\\{}\operatorname{ReflTransGen}\left(realEdge, second, first\right)) \Rightarrow\\{}\operatorname{projection}\left(first\right) = \operatorname{projection}\left(second\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/CycleCollapseProjection.cycle_segment_collapses_in_partialOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a partially ordered logical carrier and a projection that sends every realization edge to a nondecreasing logical step. Supply reachable paths in both directions between two realization states.

The projected endpoints are then ordered in both directions, so partial-order antisymmetry identifies them. The theorem does not identify the original states unless projection injectivity is separately assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/CycleCollapseProjection.cycle_segment_collapses_in_partialOrder`
