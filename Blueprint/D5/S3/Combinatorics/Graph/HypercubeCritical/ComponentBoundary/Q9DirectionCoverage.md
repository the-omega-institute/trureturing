# Two-axis and five-axis restrictions

## Abstract

Direction coverage in induced components of the nine-cube

**Theorem 1.1 (A singular two-axis mask forces a turn).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_pair_directions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_pair_directions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a fixed actual component, a mask of two directions with singular Huang Gram defect forces a vertex incident with both directions. Without such a vertex the masked edges form a matching, and the two parity degree bounds have product at most one.

**Theorem 1.2 (A singular five-axis mask forces three directions at one vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_three_directions_in_five_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_three_directions_in_five_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If all vertices had at most two neighbors within a mask of five axes, the product of the degree bounds would be at most four. This is below the mask size, so a singular defect forces a vertex with at least three active directions.

**Theorem 1.3 (A five-axis mask singular on a fixed parity contains a whole direction triple in a subcubic component).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_direction_type_in_five_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_direction_type_in_five_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an actual subcubic component and a parity. If the masked Huang Gram defect is singular on that parity for a mask of five axes, some vertex in the component has exactly three neighbors in the component, and all three of its directions lie inside the mask.

**Theorem 1.4 (Two actual components of a 258-point candidate satisfy both coverage conditions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_two_direction_covering_components`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_two_direction_covering_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any 258-point subset of the nine-cube inducing maximum degree at most three has two distinct actual connected components in which every direction pair meets at a vertex and every five-axis set contains a complete three-direction type. The components are selected before the masks, so both coverage conditions hold throughout each of the two components.

In each component, a pair can be covered by the direction set of any actual vertex that contains both axes. Each five-axis set must contain the whole direction triple of an actual degree-three vertex. Relabeling the axes preserves both conditions. These restrictions apply to candidates for Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_direction_type_in_five_mask`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_pair_directions`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_three_directions_in_five_mask`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage.exists_two_direction_covering_components`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram](Q9MaskedGram.md)
