# Distances to the leaves of a complete binary tree

## Abstract

The dyadic distance sum in a complete binary tree.

**Theorem 1.1 (The exact dyadic weight of all leaves).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance.weighted_leaf_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance.weighted_leaf_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Label every vertex by a Boolean word of length at most k, and connect it to the words obtained by appending one bit. The depth-k leaf list contains each depth-k word exactly once. For a vertex at depth d, weight each leaf by one half raised to the graph distance from that vertex. The total is three halves minus one half raised to the power (d + 1).

The distance is the number of edges from the starting word back to the longest common prefix and then forward to the target word. Transport the existing shortest pop and append paths to graph walks, preserving their lengths and the depth bound. At the root all leaves contribute a total of one. At a non-root vertex, the same first-bit branch retains the shorter-tree sum. All leaves in the other branch pass through the root and contribute one half raised to the power (d + 1). Induction then evaluates the geometric sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance.weighted_leaf_distance`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry](../Walks/BinaryWordGeometry.md)
