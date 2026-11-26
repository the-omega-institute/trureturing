# The same two components supply both parities

## Abstract

Minimum displacements of actual components in the nine-cube problem.

**Theorem 1.1 (Minimum distance and displacement bounds for a 258-point support).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ActualMinimumDisplacements.exists_two_components_with_minimum_displacement_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ActualMinimumDisplacements.exists_two_components_with_minimum_displacement_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose two actual components with universally singular weighted defects. The minimum distance between this pair is two, three, or four. On each starting parity that realizes that distance, there are at least six, ten, or fifteen distinct displacements, respectively. At equality the displacements are all the subsets of the required size on a common set of two more axes.

The positive Gram eigenvalue transfers to the opposite parity by multiplying its eigenvector by the transpose of the signed biadjacency. The transpose is the other parity's signed biadjacency after reindexing. Positivity and connectedness then supply an ambient vector with full support on whichever parity the distance requires. Thus the minimum distance, both parity sides, and the independently chosen weightings refer to the same pair of components. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ActualMinimumDisplacements.exists_two_components_with_minimum_displacement_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance](CubicContactDistance.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator](Q9MinimumDistanceOperator.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions](Q9SaturatedContactCompanions.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity](../../Translation/Q9TranslationAperiodicity.md)
