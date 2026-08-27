# Well-Founded Frontier

## Abstract

Every nonempty pending set has an executable node under a well-founded prerequisite relation.

**Theorem 1.1 (A well-founded nonempty pending set has a frontier node).**

$$\forall edge: V \to V \to Prop, pending: \operatorname{Set}\left(V\right),\\{}(\operatorname{WellFounded}\left(edge\right) \land \operatorname{Nonempty}\left(pending\right)) \Rightarrow\\{}\operatorname{Nonempty}\left(\operatorname{executableFrontier}\left(edge, \operatorname{complement}\left(pending\right), pending\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier.complement_frontier_nonempty_of_wellFounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the prerequisite relation is well-founded and the pending set is nonempty. A minimal pending element has no pending prerequisite.

That element witnesses nonemptiness of the executable frontier over the pending complement. No finiteness or linear order is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier.complement_frontier_nonempty_of_wellFounded`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier](../DagSemantics/ExecutableFrontier.md)
