# Fiber-Internal Paths

## Abstract

Paths whose edges stay inside readout fibers cannot change the observed coordinate.

**Theorem 1.1 (Fiber-internal paths preserve the readout).**

$$\forall edge: State \to State \to Prop, readout: \operatorname{Concept}\left(State, Coordinate\right),\\{}first, last: State, (\operatorname{FiberInternal}\left(edge, readout\right) \land \operatorname{ReflTransGen}\left(edge, first, last\right)) \Rightarrow\\{}\operatorname{readout}\left(first\right) = \operatorname{readout}\left(last\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/FiberInternalPaths.readout_eq_of_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify a state relation and a readout, and assume every direct edge stays inside one readout fiber. A reflexive-transitive path then connects states with equal readout values.

The conclusion states equality only for the supplied path endpoints. It does not assert that equal readouts create a path in the reverse direction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/FiberInternalPaths.readout_eq_of_reachable`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
