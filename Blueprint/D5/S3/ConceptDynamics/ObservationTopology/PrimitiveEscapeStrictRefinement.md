# Primitive Escape as Strict Refinement

## Abstract

Primitive escape is exactly strict refinement of family observation topology.

**Theorem 1.1 (Primitive escape is exactly strict observation refinement).**

$$\begin{gathered}\forall Gamma: \operatorname{Set}\left(\operatorname{Concept}\left(X, InputOutput\right)\right), candidate: \operatorname{Concept}\left(X, Output\right),\\{}\operatorname{Nonempty}\left(X\right) \Rightarrow\\{}(\operatorname{PrimitiveEscape}\left(Gamma, candidate\right) \iff \operatorname{StrictObservationRefinement}\left(\operatorname{partitionTopology}\left(\operatorname{familyReadout}\left(Gamma\right)\right), \operatorname{partitionTopology}\left(\operatorname{extendedFamilyReadout}\left(Gamma, candidate\right)\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement.primitiveEscape_iff_strict_topology_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old family readout records every definition in Gamma. The extended readout pairs those coordinates with the candidate value.

Every old observation-open set remains open after extension because the old readout is the first projection of the extended readout.

A primitive escape separates two states on which all old definitions agree, producing an open candidate fiber unavailable to the old topology. Conversely, failure of primitive escape makes the candidate fiber-constant and leaves both topologies equal.

The biconditional is asserted only under the displayed inhabited-state hypothesis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement.primitiveEscape_iff_strict_topology_refinement`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/SemanticClosureTopologyInvariance](SemanticClosureTopologyInvariance.md)
- Dependency: [D5/S3/ConceptDynamics/Topology/ContinuousRefinementObservationTopology](../Topology/ContinuousRefinementObservationTopology.md)
