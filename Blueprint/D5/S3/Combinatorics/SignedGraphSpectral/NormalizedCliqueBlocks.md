# Normalized clique blocks

## Abstract

The normalized matrix equality and its rooted zero-sum extensions.

**Theorem 1.1 (Clique decomposition and extension from each root block).**

Lean statement: `D5/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks.normalized_decomposition_with_extensions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks.normalized_decomposition_with_extensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fu-Tao Hu, Ya-Yang Liu and Yi Wang (2026). *Extremal graphs for a conjecture on the square energy of graphs*. DOI: [10.48550/arXiv.2608.17329](https://doi.org/10.48550/arXiv.2608.17329). URL: <https://arxiv.org/abs/2608.17329v1>.

*Commentary.*

For a supported doubly nonnegative matrix on a finite connected graph, assume total entry mass and twice the square-root edge mass both equal the graph budget 2m − n + 1. The matrix is the sum of normalized rank-one clique matrices. Every edge belongs to precisely one block.

Choosing any block as root supplies an extension of each zero-sum root vector to a vector with zero sum on every block. Every vertex maps into the root, and an edge joining distinct fibers lies in the root. If every block is an edge, the original graph is a tree.

## References

- Truth anchor: `D5/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks.normalized_decomposition_with_extensions`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Cuts](../Graph/Brooks/Cuts.md)
- Dependency: [D5/S3/Combinatorics/SignedGraphSpectral/DoublyNonnegativeEdgeMass](DoublyNonnegativeEdgeMass.md)
