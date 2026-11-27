# Local geometry at a crossing edge

## Abstract

Unshared distance-three contacts constrain the degrees of active exterior rows.

**Theorem 1.1 (Two occupied and two inactive exterior neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary.active_boundary_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary.active_boundary_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider two induced cubic supports at mutual separation at least three, with disjoint occupied directions at every distance-three contact. Assume the first support is balanced. An exterior vertex is active if it has a neighbor in the other exterior. Comparing the agreeing axes at two contacts forces the other occupied midpoint of any pair of support neighbors of an active vertex. Three support neighbors would give an occupied six-cycle, so evenness leaves exactly two. The two remaining common occupied directions produce exterior neighbors. If either were active, its additional occupied midpoint would close a square.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary.active_boundary_degrees`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections](Q9DistanceThreeUnsharedDirections.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount](Q9ExteriorEdgeLiftCount.md)
