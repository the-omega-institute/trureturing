# Dominator Cut

## Abstract

A dominator is a vertex whose deletion cuts every rooted path to its target.

**Theorem 1.1 (Deleting a proper dominator makes the target unreachable).**

$$\begin{gathered}\forall edge: V \to V \to \operatorname{Prop},\\{}root, u, v: V,\\{}(\operatorname{Dominates}\left(root, edge, u, v\right) \land u \neq v) \Rightarrow\\{}\neg \operatorname{Nonempty}\left(\operatorname{DirectedPath}\left(\operatorname{deleteVertex}\left(edge, u\right), root, v\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/DominatorCut.unreachable_after_delete_of_dominates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dominates means that every directed path from the root to the target contains the designated vertex.

Deleting that vertex retains only edges whose endpoints are both different from it. Any path in the deleted graph maps back to an original path that avoids the deleted vertex.

When the dominator is distinct from the target, such an avoiding path contradicts dominance. Therefore the deleted graph has no rooted directed path to the target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/DominatorCut.unreachable_after_delete_of_dominates`
