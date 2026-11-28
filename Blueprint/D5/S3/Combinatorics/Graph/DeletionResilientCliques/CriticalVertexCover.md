# Small witnesses for vertex-cover number

## Abstract

A lower bound on the vertex-cover number has a small supporting subgraph.

**Theorem 1.1 (Small witnesses for vertex-cover number).**

Lean statement: `D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover.exists_small_cover_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover.exists_small_cover_witness` (`✓ std3`). ∎

*Citation.* Paul Erdős, Tibor Gallai (1961). *On the minimal number of vertices representing the edges of a graph*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

For a finite graph G and a positive integer r at most its vertex-cover number, there is a subgraph with vertex-cover number exactly r and at most 2r nonisolated vertices. Choose an edge-minimal subgraph whose cover number is at least r. Deleting one edge drops the number below r, and restoring one endpoint to a cover shows that the original number is r. For the support bound, the edge-critical condition yields Hall's inequalities between the vertices of a minimum cover and the remaining support vertices. The resulting injection bounds the support by twice the cover size.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover.exists_small_cover_witness`
