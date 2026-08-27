# Finite Ready Existence

## Abstract

Every nonempty finite pending set has a ready minimum under a topological linear order.

**Theorem 1.1 (A nonempty finite pending set has an executable node).**

$$\forall edge: V \to V \to Prop, pending: \operatorname{Finset}\left(V\right),\\{}[\operatorname{LinearOrder}\left(V\right)],\\{}(\operatorname{StrictDependencyCoordinate}\left(edge, id\right) \land \operatorname{Nonempty}\left(pending\right)) \Rightarrow\\{}\operatorname{Nonempty}\left(\operatorname{executableFrontier}\left(edge, \operatorname{complement}\left(\operatorname{coeSet}\left(pending\right)\right), \operatorname{coeSet}\left(pending\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/FiniteReadyExistence.complement_frontier_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a linearly ordered carrier, assume every dependency edge strictly increases the identity coordinate. A nonempty finite pending set then has a minimum with no pending prerequisite.

That minimum witnesses nonemptiness of the executable frontier over the pending complement. Finiteness is carried by the Finset binder and the linear order remains an instance binder.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/FiniteReadyExistence.complement_frontier_nonempty`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier](ExecutableFrontier.md)
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate](StrictDependencyCoordinate.md)
