# Closed-neighborhood corona blocks

## Abstract

The adjacency blocks and vertex degrees of the closed-neighborhood corona.

**Theorem 1.1 (Adjacency blocks).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.adjMatrix_corona`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.adjMatrix_corona` (`✓ std3`). ∎

*Citation.* Bishal Sonar; Ravi Srivastava (2024). *On the spectrum of closed neighbourhood corona product of graph and its application*. DOI: [10.48550/arXiv.2407.05653](https://doi.org/10.48550/arXiv.2407.05653). URL: <https://arxiv.org/abs/2407.05653v2>.

*Commentary.*

The base block is the base adjacency matrix. The cross block repeats each column of the base adjacency plus the identity for all vertices in the indexed copy. The opposite cross block is its transpose. The copy block is the Kronecker product of the base identity and the attached adjacency matrix. Sonar and Srivastava display the identity in §3.1 with the copy coordinates ordered as (attached vertex, base vertex). Swapping those coordinates for rows and columns gives the arrangement here. Lean proves the identity directly over a semiring from the corona adjacency relation.

**Theorem 1.2 (Degree of a base vertex).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.degree_corona_inl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.degree_corona_inl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A base vertex of degree d keeps its original neighbors and is adjacent to every vertex in each of d + 1 copies. If the attached graph has m vertices, its degree in the corona is d + (d + 1)m.

**Theorem 1.3 (Degree of a copy vertex).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.degree_corona_inr`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.degree_corona_inr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vertex of internal degree e in a copy at a base vertex of degree d meets the d + 1 base vertices in that closed neighborhood. Its degree is d + 1 + e.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.adjMatrix_corona`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.degree_corona_inl`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.degree_corona_inr`
