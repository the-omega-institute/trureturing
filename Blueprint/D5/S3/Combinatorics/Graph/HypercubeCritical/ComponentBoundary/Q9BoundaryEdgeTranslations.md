# Boundary-edge translations in the nine-cube

## Abstract

Boundary-edge translations in the nine-cube

Let C be a Huang-balanced induced cubic vertex set in Q₉, and let B be its exterior vertex boundary. Represent an edge of direction t by its endpoint whose t-bit is zero. The coordinate flip τᵢ toggles bit i at both endpoints. For i ≠ t it commutes with τₜ and preserves the t-bit, so the image is again an edge of direction t with the same endpoint convention.

**Theorem 1.1 (Four exterior translations per internal edge).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.card_transverseExterior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.card_transverseExterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each endpoint of an internal edge has two other internal directions. These pairs are disjoint because a direction shared by both endpoints would give a square in C, which Huang balance forbids. Of the eight transverse axes, the four remaining flips send both endpoints into B.

**Theorem 1.2 (The total number of translations with multiplicity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.card_witnesses`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.card_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 3|C| oriented incidences count each internal edge twice. Pairing each internal edge with its four exterior axes gives 6|C| edge–axis pairs.

**Theorem 1.3 (Translated images lie in the induced boundary).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.translatedEdges_subset_boundaryEdges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.translatedEdges_subset_boundaryEdges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write D for the distinct translated edges. Each image endpoint is outside C and adjacent to its original endpoint in C, so D ⊆ E(B). This containment holds for any C.

**Theorem 1.4 (A cut bound for distinct images).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.distinct_edge_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.distinct_edge_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose C ⊆ U, there are no edges from C to U ∖ C, and the induced graph on U has maximum degree at most three. Let T = Q₉ ∖ U and let q count the edges across the cut. Then B ⊆ T, 6|U| ≤ q, and q + 2|E(T)| = 9(512 − |U|). Since D ⊆ E(T), 15|U| + 2|D| ≤ 4608. Cubicity and balance of C are unnecessary for this bound.

**Theorem 1.5 (The sum of boundary-edge multiplicities).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.sum_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.sum_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For e ∈ E(B), let mₑ count the edge–axis pairs with image e. For a Huang-balanced induced cubic C, the sum of mₑ over E(B) is 6|C|.

**Theorem 1.6 (A cut bound in terms of collisions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.boundary_edge_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.boundary_edge_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the balanced cubic and cut hypotheses, let Λ be the sum of binom(mₑ, 2) over E(B), counting unordered pairs with the same image. Summing mₑ ≤ 1 + binom(mₑ, 2) over D gives 6|C| ≤ |D| + Λ. The cut bound then gives 15|U| + 12|C| ≤ 4608 + 2Λ.

**Theorem 1.7 (At least 63 collisions for a 72-vertex set).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.collisionCount_ge_63`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.collisionCount_ge_63` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If |C| = 72 and |U| ≥ 258 under the same hypotheses, then Λ ≥ 63.

The value of f₂(Q₉) remains open. Hong–Wu–Xia ask whether it is 3 or 4 in arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.boundary_edge_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.card_transverseExterior`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.card_witnesses`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.collisionCount_ge_63`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.distinct_edge_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.sum_multiplicity`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.translatedEdges_subset_boundaryEdges`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
