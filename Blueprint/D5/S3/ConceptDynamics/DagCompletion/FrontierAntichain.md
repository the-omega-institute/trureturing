# Frontier Antichain

## Abstract

An executable frontier over a predecessor-closed completed set is an antichain for strict dependency reachability.

**Theorem 1.1 (The complement frontier is a strict-reachability antichain).**

$$\begin{gathered}\forall edge: V \to V \to Prop, pending: \operatorname{Set}\left(V\right), first, second: V,\\{}(\operatorname{PredecessorClosed}\left(edge, \operatorname{complement}\left(pending\right)\right) \land\\{}first \in \operatorname{executableFrontier}\left(edge, \operatorname{complement}\left(pending\right), pending\right) \land\\{}second \in \operatorname{executableFrontier}\left(edge, \operatorname{complement}\left(pending\right), pending\right)) \Rightarrow\\{}\neg \operatorname{TransGen}\left(edge, first, second\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/FrontierAntichain.complement_frontier_strict_antichain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the complement of pending is predecessor-closed, and take two members of the executable frontier computed over that complement.

No nonempty dependency path can run from the first frontier member to the second. The closure hypothesis is essential and is displayed explicitly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/FrontierAntichain.complement_frontier_strict_antichain`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier](../DagSemantics/ExecutableFrontier.md)
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure](../DagSemantics/PrerequisiteClosure.md)
