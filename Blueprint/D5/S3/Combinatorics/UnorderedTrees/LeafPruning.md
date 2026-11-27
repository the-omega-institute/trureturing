# Leaf pruning of actual rooted trees

## Abstract

Deleting all original leaves of a finite rooted tree with an internal root leaves the actual internal-vertex subtree and lowers vertex-height by one.

**Definition 1.1 (The internal-vertex subtree).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\forall hr: \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right), \left(\operatorname{prune}\left(T, hr\right) \in \operatorname{Tree}\left(\{v: V \mid \operatorname{Internal}\left(T, v\right)\}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.prune` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parent map restricts to the original internal vertices and fixes the original root. Parent iteration commutes with subtype inclusion, so retained vertices still reach the root.

**Theorem 1.2 (The target equality supplies the internal root).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\operatorname{height}\left(T\right) = \operatorname{internalCount}\left(T\right) \Rightarrow \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.qualifying_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive vertex-height supplies an internal vertex and a nonroot child. The last nonroot vertex on the path from that child to the root is a child of the root.

**Theorem 1.3 (The exact pruning reduction).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\forall hr: \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right), \left(\operatorname{height}\left(T\right) = \operatorname{height}\left(\operatorname{prune}\left(T, hr\right)\right)+1 \land \left(\operatorname{height}\left(T\right) = \operatorname{internalCount}\left(T\right) \Leftrightarrow \operatorname{card}\left(\{v: V \mid \operatorname{Internal}\left(T, v\right)\}\right) = \operatorname{height}\left(\operatorname{prune}\left(T, hr\right)\right)+1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.pruning_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Depth is unchanged on retained vertices. Every nonroot vertex lies one level below an internal parent, and each internal vertex has a child one level below it. The pruned vertex cardinality is the original internal-vertex count.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.prune`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.pruning_reduction`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.qualifying_root`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/ParentTree](ParentTree.md)
