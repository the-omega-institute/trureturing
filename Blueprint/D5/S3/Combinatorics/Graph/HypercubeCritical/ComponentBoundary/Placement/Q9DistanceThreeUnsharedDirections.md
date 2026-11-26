# Direction partitions and two-step moves

## Abstract

Direction structure at minimum-distance-three contacts without a shared flip.

**Definition 1.1 (The axes in the contact displacements).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.unsharedContactAxes`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.unsharedContactAxes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the union of the three-axis displacements to one fixed endpoint.

**Theorem 1.2 (Five contact axes force a partition of the neighbor directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.axes_and_partition_of_unshared_contacts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.axes_and_partition_of_unshared_contacts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume both supports are balanced induced cubic sets at separation at least three. Fix an endpoint whose nearest partners at distance three all have disjoint occupied directions with it. Even exterior degree lets a contact replace each of its three differing axes. With only four axes available, the three repairs and the original endpoint would give four neighbors of one vertex. The at least five contact axes each occur an odd number of times in the six second-step directions at the fixed endpoint. Thus each of the six occurs once. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

**Definition 1.3 (Translation by the occupied directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.directionOrigin`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.directionOrigin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Flip the occupied direction axes at the given vertex.

**Theorem 1.4 (Each differing axis admits a two-step move preserving the translated vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.unshared_two_step_preserves_direction_origin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.unshared_two_step_preserves_direction_origin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume all distance-three pairs have disjoint occupied directions. For each differing axis of such a pair, the two occupied triples partition the agreeing axes. A two-step move in the second component replaces one differing axis by a first-step axis. Its direction triple exchanges the same two axes, so the translated vertex is unchanged.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.axes_and_partition_of_unshared_contacts`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.directionOrigin`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.unsharedContactAxes`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections.unshared_two_step_preserves_direction_origin`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes](../Laurent/Q9LaurentDirectionTypes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar](Q9TightContactStar.md)
