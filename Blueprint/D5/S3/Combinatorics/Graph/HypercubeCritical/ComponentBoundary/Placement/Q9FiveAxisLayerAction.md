# The action on actual supports

## Abstract

Exchanging coordinates 3 and 4 and exchanging the roots realize the two pattern permutations by actual cube isometries. Both preserve the even slice and the mask family.

**Theorem 1.1 (The action on actual supports).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisLayerAction.reaches_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisLayerAction.reaches_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping coordinates 3 and 4 fixes the root pair and the missing mask. Translation by the root displacement exchanges the roots, and exchanging the two components restores their order. The two operations commute and are involutions on the rooted layer, so each orbit has at most four patterns. The certificate cover finds six orbits among the eighteen patterns. The same operations transport actual cube supports while preserving the even slice and the mask family.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisLayerAction.reaches_representative`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitGeometry](Q9FiveAxisOrbitGeometry.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9RootStabilizer](Q9RootStabilizer.md)
