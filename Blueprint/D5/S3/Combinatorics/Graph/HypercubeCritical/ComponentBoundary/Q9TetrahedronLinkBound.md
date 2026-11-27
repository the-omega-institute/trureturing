# Incidence bound for capped tetrahedral supports

## Abstract

Incidence bound for capped tetrahedral supports

**Theorem 1.1 (Incidence bound for capped tetrahedral supports).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound.support_card_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound.support_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A triangle can never have a single coface in the support of an oriented cycle. The vertex link therefore has no edge contained in exactly one triangle.

In a link with at most five triangles every used vertex belongs to at least three of them, so the link uses at most five vertices. Complementary edges give a complete multipartite graph and the only nonempty cycle of this size is a tetrahedron boundary. The five-set cap excludes it. Counting all incidences gives at least six per used vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound.support_card_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TriangleSmallSupport](Q9TriangleSmallSupport.md)
