# Frontier Extension Closure

## Abstract

Adjoining an executable frontier preserves predecessor closure.

**Theorem 1.1 (Adding the whole frontier preserves predecessor closure).**

$$\forall edge: V \to V \to Prop, completed, pending: \operatorname{Set}\left(V\right),\\{}\operatorname{PredecessorClosed}\left(edge, completed\right) \Rightarrow\\{}\operatorname{PredecessorClosed}\left(edge, \operatorname{union}\left(completed, \operatorname{executableFrontier}\left(edge, completed, pending\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/FrontierExtensionClosure.predecessorClosed_union_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix completed and pending sets. If the completed set is closed under direct prerequisites, adjoining every node ready over that set preserves the same closure property.

A prerequisite of an old completed node is supplied by the closure hypothesis; a prerequisite of a frontier node is already completed by readiness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/FrontierExtensionClosure.predecessorClosed_union_frontier`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier](ExecutableFrontier.md)
