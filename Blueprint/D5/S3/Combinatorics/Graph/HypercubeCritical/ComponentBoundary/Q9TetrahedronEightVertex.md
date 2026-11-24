# The eight-vertex obstruction for twelve capped tetrahedra

## Abstract

The eight-vertex obstruction for twelve capped tetrahedra

**Theorem 1.1 (Eight used vertices are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEightVertex.tetrahedra_card_ne_twelve_on_eight_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEightVertex.tetrahedra_card_ne_twelve_on_eight_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twelve tetrahedra have forty-eight vertex incidences. On eight used vertices, the six-triangle lower bound therefore holds with equality in every link. Each link is a triangular bipyramid with five vertices and nine edges.

Each vertex of the support graph has five neighbors, so its complement is 2-regular with eight edges. Removing a vertex and its two complement neighbors removes at most four of those edges. At most six support edges remain among the five original neighbors, contradicting the bipyramid.

This rules out an eight-vertex twelve-facet support in the sharp contact-shell reduction of Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEightVertex.tetrahedra_card_ne_twelve_on_eight_vertices`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CappedTriangleLinkFive](Q9CappedTriangleLinkFive.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound](Q9TetrahedronLinkBound.md)
