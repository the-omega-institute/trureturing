# At least eight masks for an actual distance-two pair

## Abstract

An actual component pair at distance two realizes at least eight masks on each nonempty starting parity.

**Theorem 1.1 (At least eight masks for an actual distance-two pair).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoAperiodic.exists_actual_pair_with_eight_masks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoAperiodic.exists_actual_pair_with_eight_masks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the actual pair by universal signed singularity. The distance-three and distance-four exclusions apply to the same components. Each axis in the contact graph belongs to three or more masks, so seven masks could use only four axes and there would be room for only six edges. The opposing-star refutations exclude six. This leaves at least eight masks on every nonempty starting parity of the chosen pair. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoAperiodic.exists_actual_pair_with_eight_masks`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion](Q9DistanceThreeExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph](Q9EightMaskGraph.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoReplay](Q9TightDistanceTwoReplay.md)
