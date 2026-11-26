# Reduce the nine-cube problem to distance two

## Abstract

In a hypothetical subcubic 258-vertex restriction of the nine-cube, the two balanced cubic components have minimum distance two.

**Theorem 1.1 (Minimum distance three is excluded).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion.no_minimum_distance_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion.no_minimum_distance_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shared occupied direction is impossible by the normalized finite refutations. The remaining distance-three pairs have disjoint occupied directions. The exterior edge budget excludes that configuration in the proposed restriction.

**Theorem 1.2 (The two balanced components have minimum distance two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion.exists_two_balanced_components_at_distance_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion.exists_two_balanced_components_at_distance_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Huang's signing extracts two distinct balanced induced cubic components from a subcubic 258-vertex candidate for Hong–Wu–Xia Problem 2. Their minimum distance belongs to two, three or four. The two exclusion proofs leave distance two. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion.exists_two_balanced_components_at_distance_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion.no_minimum_distance_three`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion](Q9DistanceFourExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedExclusion](Q9DistanceThreeUnsharedExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay](Q9SharedContactGeometryReplay.md)
