# Cutting off a child subtree

## Abstract

The components obtained by deleting a parent edge in a finite binary tree.

**Definition 1.1 (Membership in the selected child subtree).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/WordTreeCut.belowChild`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/WordTreeCut.belowChild` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex belongs to the child subtree when its word has the child word as a prefix. The child word is the parent word followed by the chosen bit.

**Theorem 1.2 (Reachability is equality of subtree membership after the cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/WordTreeCut.bounded_reachable_after_extension_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/WordTreeCut.bounded_reachable_after_extension_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a depth cap, a parent vertex and a chosen bit with its child still inside the depth cap. Delete the edge joining parent and child. Two vertices are reachable from one another exactly when they agree on membership in the selected child subtree.

An edge crossing the prefix boundary must join the selected child to its parent. Hence every remaining walk preserves membership. Inside the subtree, each vertex connects to the child by a chain of extensions. Outside the subtree, each vertex connects to the empty word by a chain of extensions. These chains respect the depth cap and avoid the deleted edge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/WordTreeCut.belowChild`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/WordTreeCut.bounded_reachable_after_extension_cut`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance](BinaryTreeLeafDistance.md)
