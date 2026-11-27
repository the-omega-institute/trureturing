# Leaf pruning of actual rooted trees

## Abstract

Deleting all original leaves of a finite rooted tree with an internal root leaves the actual internal-vertex subtree and lowers vertex-height by one.

**Definition 1.1 (The internal-vertex subtree).**

$$\operatorname{prune}\left(T, h\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.prune` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assume h says that the root of T has a child. The pruned carrier is precisely the subtype of original internal vertices. Its parent map is the original parent map restricted to this subtype, and its root is the original root. The parent of every nonroot vertex is internal; at the root closure follows from h. Parent iteration commutes with the subtype inclusion, proving that every retained vertex still reaches the root.

**Theorem 1.2 (The target equality supplies the internal root).**

$$\operatorname{height}\left(T\right)=\operatorname{internalCount}\left(T\right) \to \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.qualifying_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vertex-height is positive. Thus equality with the internal-vertex count supplies an internal vertex and one of its nonroot children. On the path from that child to the root, the last nonroot vertex is a child of the root. Consequently every tree satisfying the equality can be pruned on a nonempty rooted carrier; the singleton does not create an exceptional qualifying case.

**Theorem 1.3 (The exact pruning reduction).**

$$\operatorname{height}\left(T\right)=\operatorname{height}\left(\operatorname{prune}\left(T, h\right)\right)+1 \land (\operatorname{height}\left(T\right)=\operatorname{internalCount}\left(T\right) \iff \operatorname{card}\left(\operatorname{Internal}\left(T\right)\right)=\operatorname{height}\left(\operatorname{prune}\left(T, h\right)\right)+1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.pruning_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type and every rooted parent tree T whose root is internal, pruning lowers vertex-height by exactly one. Depth is unchanged on retained vertices because all parent iterates agree. Every nonroot original vertex lies one level below an internal parent, giving the upper height bound. Conversely each retained vertex has a child one level below it, giving the reverse bound. The pruned vertex cardinality is the original internal-vertex count, so the equality defining the counting problem becomes size of the pruned tree equals its vertex-height plus one.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.prune`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.pruning_reduction`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafPruning.qualifying_root`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/ParentTree](ParentTree.md)
