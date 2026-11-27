# Ten masks at a distance-two contact

## Abstract

In any 258-vertex subcubic induced candidate, the actual saturated pair realizes at least ten masks on each parity for which a distance-two contact occurs.

**Theorem 1.1 (Ten masks at a distance-two contact).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoTenMasks.exists_actual_pair_with_ten_masks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoTenMasks.exists_actual_pair_with_ten_masks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distance-three and distance-four exclusions leave an actual component pair at distance two. Weighted saturation forces at least three partners at each active axis. At nine masks, the five-axis family is a complete graph with one missing edge and the six-axis family is complete bipartite. The rooted group action and the six-axis rectangle contradiction exclude these alternatives, raising the lower bound from nine masks to ten. This is a restriction on candidates in Hong, Wu and Xia's Problem 2 (arXiv:2610.09483).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoTenMasks.exists_actual_pair_with_ten_masks`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NineMaskExclusion](Q9NineMaskExclusion.md)
