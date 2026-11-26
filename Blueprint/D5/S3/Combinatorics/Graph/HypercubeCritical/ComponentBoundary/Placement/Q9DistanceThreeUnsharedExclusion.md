# Exclusion of unshared minimum-distance-three contacts

## Abstract

The omitted-edge budget excludes the all-unshared minimum-distance-three case.

**Theorem 1.1 (No unshared minimum-distance-three configuration).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedExclusion.no_unshared_distance_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedExclusion.no_unshared_distance_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a 258-vertex induced subcubic restriction, take two closed balanced cubic supports of size at least 48 that are mutually separated by at least three. A distance-three contact with all distance-three pairs using disjoint occupied directions would force at least 104 edges inside each exterior and at least 162 edges between the two exteriors. These disjoint exteriors lie in the complement, which would contain at least 370 edges against its cap of 369. This excludes one branch of Hong–Wu–Xia Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedExclusion.no_unshared_distance_three`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget](Q9ComplementBoundaryBudget.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary](Q9DistanceThreeActiveBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeCrossingCount](Q9DistanceThreeCrossingCount.md)
