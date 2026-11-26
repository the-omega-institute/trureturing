# Simultaneous flips at minimum distance four

## Abstract

Exclusion of minimum distance four between balanced cubic nine-cube supports.

**Theorem 1.1 (Minimum distance four is impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion.no_distance_four_of_four_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion.no_distance_four_of_four_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an endpoint in the second support. At distance four, each endpoint has three occupied directions among the five agreeing axes. A common direction flips both endpoints and preserves their displacement. The absence of a square makes the union of directions at the two adjacent vertices in the second support equal to the five agreeing axes. Thus each direction at the fixed endpoint determines at most one contact, giving at most three. Flipping each of the four differing axes reaches an exterior vertex. Evenness gives another occupied neighbor that is again at distance four and agrees with the fixed endpoint on precisely that one of the four original differing axes. This gives four distinct contacts.

**Theorem 1.2 (The two balanced components have minimum distance two or three).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion.exists_two_components_at_distance_two_or_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion.exists_two_components_at_distance_two_or_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the hypothetical subcubic 258-vertex branch of Hong–Wu–Xia Problem 2, the closest pair of the two extracted balanced cubic components has distance at least two. The five-axis agreement bound gives distance at most four, and the fixed-endpoint argument excludes four. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion.exists_two_components_at_distance_two_or_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion.no_distance_four_of_four_separated`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance](CubicContactDistance.md)
