# A complete correspondence in every dimension

## Abstract

All nonzero binary vectors and the actual line subgraph.

**Definition 1.1 (Actual one-dimensional Submodules).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/BinaryLineGraph.graphIso`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/BinaryLineGraph.graphIso` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

For every natural n, map a nonzero binary coordinate vector to its actual one-dimensional span. Every line is obtained, and over ZMod2 two nonzero vectors with the same span are equal. The resulting bijection preserves distinct-dot-zero adjacency in both directions. The target is the graph induced on every line of NikandishClique.orthogonalityGraph n; there is no restriction to coordinate lines, chosen representatives or a subfamily. The empty n=0 domain is included. The immediate consumer is the complete six-dimensional line chromatic theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/BinaryLineGraph.graphIso`
- Dependency: [D5/S3/Combinatorics/Orthogonality/NikandishClique](NikandishClique.md)
