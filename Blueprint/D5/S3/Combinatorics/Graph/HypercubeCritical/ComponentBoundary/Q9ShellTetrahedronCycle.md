# Minimum order, equality and the ten-facet gap

## Abstract

The minimum capped tetrahedral cycle

**Theorem 1.1 (At least nine tetrahedra).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.nine_le_card_tetrahedron_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.nine_le_card_tetrahedron_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex links are mod-two triangle cycles. Each nonempty link has even size and a four-triangle link would be a tetrahedron boundary. Adding the linked vertex would put four selected tetrahedra in one five-set.

There are at least six used vertices and at least six tetrahedra through each of them. Counting vertex incidences gives at least nine tetrahedra.

**Theorem 1.2 (The equality case).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.tetrahedron_cycle_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.tetrahedron_cycle_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With nine tetrahedra there are six used vertices. Complement the tetrahedra among those six vertices and read the complementary pairs as edges. Each triple contains an even number of edges, so the graph is a cut. Its nine edges give two parts of size three.

This cycle arises from the complement of a translated four-element shell of paired fibres in Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.3 (Ten tetrahedra are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.ten_ne_card_tetrahedron_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.ten_ne_card_tetrahedron_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The incidence bound confines an order-ten cycle to six used vertices. The complementary graph would be a cut with ten edges, but the largest cut on six vertices has nine edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.nine_le_card_tetrahedron_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.ten_ne_card_tetrahedron_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle.tetrahedron_cycle_equality`
