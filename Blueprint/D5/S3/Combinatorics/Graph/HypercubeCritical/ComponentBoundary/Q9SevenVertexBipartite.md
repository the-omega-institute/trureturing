# Eleven edges force a bipartition of sizes four and three

## Abstract

A dense triangle-free graph on seven vertices

**Theorem 1.1 (The neighbors of a maximum-degree vertex form the four-vertex part).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite.seven_vertex_bipartition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite.seven_vertex_bipartition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A triangle-free simple graph on seven vertices with at least eleven edges has complementary independent parts of sizes four and three.

The degree sum gives a vertex with at least four neighbors. Its neighborhood is independent. An edge in the complement would use the two vertices there other than the chosen vertex. Its endpoints have disjoint neighborhoods in the four-vertex part, leaving at most eight crossing edges and one internal edge in total. With both parts independent, the product of their sizes must reach eleven, forcing the sizes four and three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite.seven_vertex_bipartition`
