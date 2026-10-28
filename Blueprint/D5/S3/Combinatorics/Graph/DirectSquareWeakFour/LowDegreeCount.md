# Boundary charging for degree-two vertices

## Abstract

Boundary charging for degree-two vertices

All graphs in these statements are finite simple graphs. The low set need not be connected and may be empty. The estimates count actual neighbor incidences.

**Definition 1.1 (Neighbors in a set).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.neighborsIn`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.neighborsIn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

neighborsIn G A v is the subset of A adjacent to v.

**Theorem 1.2 (Two orders of incidence counting).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.sum_neighborsIn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.sum_neighborsIn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite vertex sets A,B and natural vertex weights f, the sum over v in A and neighbors w in B of f w equals the sum over w in B of f w times the number of its neighbors in A.

**Theorem 1.3 (Low vertices and outgoing edges).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.low_boundary_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.low_boundary_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L consist of degree-two vertices. Suppose that whenever two vertices of L are adjacent and the first has two neighbors in L, the second has at most one. Then twice the number of vertices in L is at most three times the number of edges from L to its complement. A local charge is summed; its internal transfers cancel by symmetry.

**Theorem 1.4 (Boundary capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.boundary_le_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.boundary_le_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex set L, its outgoing-edge count is bounded by the total degree of vertices in its complement.

**Theorem 1.5 (Twelve-elevenths edge bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.excess_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.excess_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite simple graph of minimum degree at least two satisfying the stated local condition on its degree-two vertices has at least twelve elevenths as many edges as vertices. Split vertices into low and high sets. The low-boundary estimate and minimum high degree three combine with the degree-sum identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.boundary_le_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.excess_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.low_boundary_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.neighborsIn`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.sum_neighborsIn`
