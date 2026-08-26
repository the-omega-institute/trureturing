# Executable Frontier

## Abstract

The executable frontier consists of pending nodes whose direct prerequisites are complete.

**Theorem 1.1 (The complement frontier is exactly the ready pending set).**

$$\forall edge: V \to V \to Prop, pending: \operatorname{Set}\left(V\right), node: V,\\{}node \in \operatorname{executableFrontier}\left(edge, \operatorname{complement}\left(pending\right), pending\right) \iff\\{}(node \in pending \land \forall prerequisite: V, \operatorname{edge}\left(prerequisite, node\right) \Rightarrow \neg (prerequisite \in pending)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier.mem_frontier_complement_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A node belongs to the frontier computed over the complement of pending exactly when it is pending and none of its direct prerequisites remain pending.

The equivalence unfolds the definitions of executableFrontier and ReadyOver. It concerns direct prerequisites and does not replace them with arbitrary reachable ancestors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier.mem_frontier_complement_iff`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure](PrerequisiteClosure.md)
