# Actual subdivision and hair-tree grafting

## Abstract

Actual subdivision and hair-tree grafting

**Definition 1.1 (Grafting into an actual edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/BranchingHairTree.graft`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/BranchingHairTree.graft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any actual cyclic flag graph G, any flag a of G, and any finite open flag structure T : OpenHair, graft subdivides the actual paired edge containing a by a new trivalent vertex and connects T.root to that vertex. The generic definition does not require T to be acyclic. This delivery uses it with T = t.model for a finite ordinary colored binary tree t. Every existing flag, cyclic order and leaf label remains in the graph, including every numbered exterior anchor. The new pairing is explicitly involutive with no fixed point. In particular, the stem of a two-leaf tree has a genuine trivalent parent; an isolated colored Y with no such parent is outside this construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/BranchingHairTree.graft`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/CyclicFlagDiagram](CyclicFlagDiagram.md)
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/HairTreeShape](HairTreeShape.md)
