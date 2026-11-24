# The eleven-facet gap for capped tetrahedral supports

## Abstract

The eleven-facet gap for capped tetrahedral supports

**Theorem 1.1 (The eleven-facet gap for capped tetrahedral supports).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven.tetrahedra_card_ne_eleven`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven.tetrahedra_card_ne_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If there were eleven tetrahedra, the vertex-link incidence bound would confine the support to six or seven vertices. On six vertices, every tetrahedron is in two five-sets. The six five-sets can accommodate only eighteen incidences, whereas eleven tetrahedra would require twenty-two.

On seven vertices, double counting finds a vertex occurring at least seven times. A coordinate permutation moves it to the chosen pivot. After taking complements, the pairs through that pivot form a graph with at most four edges. The pair cap forces a three-spoke star or a four-cycle. Its isolated vertices force all remaining triples, giving nine or twelve facets.

The argument applies to the support of an oriented real cycle since a singleton coface cannot cancel in its boundary. For sharp contact blocks in the Q9 question, the shell is obtained by XOR translation on the transverse coordinates, followed by complementation. Hong, Wu and Xia's Problem 2 asks about the full 258-point candidate. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.2 (The twelve-triple normal form).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven.card_eq_nine_or_twelve_with_pivot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven.card_eq_nine_or_twelve_with_pivot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pivot with at most four incident triples determines the whole twelve-triple family. Every triple consists of an edge of a four-cycle and one of the three vertices off the cycle, including the pivot. Complementation on seven vertices gives the join of a triangle boundary and a four-cycle.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven.card_eq_nine_or_twelve_with_pivot`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven.tetrahedra_card_ne_eleven`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport](Q9SparseCocycleSupport.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound](Q9TetrahedronLinkBound.md)
