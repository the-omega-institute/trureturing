# The first cardinality gap of signed two-contact columns

## Abstract

The first cardinality gap of signed two-contact columns

**Theorem 1.1 (Nonadjacent columns share at most two distance-two neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap.card_commonColumns_of_nonadj_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap.card_commonColumns_of_nonadj_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two nonadjacent columns with a common neighbor differ on four axes. The six possible intermediate labels form the octahedron graph on two-element subsets. Three intermediate columns would give a neighborhood vertex adjacent to two others, incompatible with the disjoint pairs arising from occupied partners.

**Theorem 1.2 (At least nine columns and no ten-column case).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap.cardinality_gap_of_twoContact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap.cardinality_gap_of_twoContact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The induced distance-two graph is four-regular. Counting two-step paths gives a lower bound of eleven minus the number of three-contact occupied rows at each column. This number is at most two, so the column count is at least nine.

At ten columns the permutation-cover inequality and triangle incidence force eight columns incident to two triangles. Removing triangle edges would leave a simple two-regular graph on the remaining two vertices, a contradiction. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap.card_commonColumns_of_nonadj_le_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap.cardinality_gap_of_twoContact`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders](PrimeContactCubeOrders.md)
