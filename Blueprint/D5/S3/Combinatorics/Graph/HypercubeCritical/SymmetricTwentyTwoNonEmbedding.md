# Symmetric Twenty Two Non Embedding

## Abstract

Symmetric Twenty Two Non Embedding

Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external problem and its published results belong to that paper. This repository proof addresses a local structural branch; no solution of the original 258-point problem or literature priority is claimed. The original problem remains unresolved.

The explicit twenty-two-vertex, twenty-nine-edge candidate has no induced embedding in a finite Boolean cube of any dimension. Each coordinate cut obeys short-path constraints; a kernel-checked parity consequence contradicts the three distinguished edges. The statement concerns this explicit candidate, not all symmetric slices until the actual-classification bridges are applied.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist n and an injective vertex map from the explicit twenty-two-vertex graph into the n-dimensional Boolean cube that preserves and reflects adjacency.

**Theorem 1.2 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem has literally type Not claim, excluding this explicit candidate in every finite cube dimension by coordinate-cut parity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding](AsymmetricSliceNonEmbedding.md)
