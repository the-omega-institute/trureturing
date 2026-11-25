# Nine-column equality and its cube grid

## Abstract

Nine-column equality and its cube grid

**Theorem 1.1 (Nine columns are exactly a grid from two disjoint three-axis sets).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity.eq_nineGrid_of_twoContact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity.eq_nineGrid_of_twoContact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality in the two-step count forces two occupied partner pairs at the root. The two triples of their axes are disjoint. Each choice of one neighbor from each pair has a unique nonadjacent rectangle completion, yielding all nine vertices.

**Theorem 1.2 (The actual empty directions and occupied center are determined).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity.nine_column_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity.nine_column_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed square equations determine the empty directions as the other two axes of each triple. Thus the occupied center is constant across the grid. Hamming distance is twice the number of changed grid factors.

For the paired-fibre branch of Hong, Wu and Xia's Problem 2, the nine-column case belongs to the rigid common-center shell geometry. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity.eq_nineGrid_of_twoContact`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity.nine_column_equality`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap](PrimeContactCardinalityGap.md)
