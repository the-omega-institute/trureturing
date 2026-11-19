# Finite chains of suspension moves

## Abstract

Finite chains of suspension moves

**Definition 1.1 (Literal operation chains).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves.MoveChain`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves.MoveChain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A chain is built from identity, triple-subdivision, matching and Lozin constructors. Every constructor contains its chosen vertices, adjacency or neighborhood-partition proofs, and an actual relabeling equivalence.

**Definition 1.2 (The iterated shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves.reducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves.reducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A chain of n moves from G to F gives reduced integral singular homology of the actual F-independence realization in degree q+n isomorphic to that of G in degree q, for q at least one.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves.MoveChain`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves.reducedHomologyIso`
- Dependency: [D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin](FiniteGraphSuspensionMoves/Lozin.md)
