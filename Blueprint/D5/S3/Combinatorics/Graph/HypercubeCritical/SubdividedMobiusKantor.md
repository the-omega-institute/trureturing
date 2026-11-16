# Subdivided Mobius Kantor

## Abstract

Subdivided Mobius Kantor

Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external problem and its published results belong to that paper. This repository proof addresses a local structural branch; no solution of the original 258-point problem or literature priority is claimed. The original problem remains unresolved.

The graph consists of a step-one eight-cycle on vertices 0 through 7, a step-three eight-cycle on vertices 8 through 15, and eight subdivided rungs through vertices 16 through 23. It has twenty-four vertices and thirty-two edges. An induced cube embedding would make every coordinate cut an induced matching. The real two-edge and three-edge paths force even crossing parity on the edges (0,1), (3,19), and (10,18). Each cube edge has exactly one direction, so three such direction indicators cannot sum to zero. The proof uses ordinary Lean kernel proof terms; no SAT answer or external cut catalog is trusted. This excludes the explicit candidate in the remaining (12,12;4,4) slice branch, without classifying all graphs with those parameters.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist n and an injective vertex map from the subdivided Mobius-Kantor graph into the n-dimensional Boolean cube that preserves and reflects adjacency.

**Theorem 1.2 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem has literally type Not claim, excluding this explicit candidate in every finite cube dimension by coordinate-cut parity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding](AsymmetricSliceNonEmbedding.md)
