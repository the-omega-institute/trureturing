# Permutation coverage for two-contact Huang cube columns

## Abstract

Permutation coverage for two-contact Huang cube columns

**Theorem 1.1 (The source axes of an occupied partner count its other contacts).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.card_rowContacts_of_occupied`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.card_rowContacts_of_occupied` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The other column at an empty row determines an occupied partner axis at the original column. The opposite corner of the square gives a bijection from the empty source directions with that partner to the other contacts of the occupied row.

**Theorem 1.2 (Three-axis stars correspond to three-contact occupied rows).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.tripleCount_eq_card_threeContactRowsAt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.tripleCount_eq_card_threeContactRowsAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fibers of the partner map are disjoint. Each fiber together with its occupied target forms one coordinate block. A block has size three precisely when its target row has three selected contacts.

**Theorem 1.3 (The weighted permutation cover is a necessary cube contact bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.weighted_order_coverage_of_cube`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.weighted_order_coverage_of_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With four empty directions per selected column, exactly two contacts at each incident empty row, and at most three at occupied rows, there are four source axes. The partner blocks all have size two or three and carry the integer exponent steps. The permutation covering theorem gives 144 as a lower bound for the weighted sum of the three column counts.

This supplies a structural obstruction for the two-contact case in Hong, Wu and Xia's open nine-cube Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.card_rowContacts_of_occupied`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.tripleCount_eq_card_threeContactRowsAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders.weighted_order_coverage_of_cube`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeLift](PrimeContactCubeLift.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage](PrimeContactOrderCoverage.md)
