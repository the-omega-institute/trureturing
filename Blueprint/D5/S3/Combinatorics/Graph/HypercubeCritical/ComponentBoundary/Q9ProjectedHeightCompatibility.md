# Box centers are invariant along paths in the Laurent projection

## Abstract

Integer heights constrain the centers and splits of six-dimensional cube boxes.

**Theorem 1.1 (Overlap and a common height determine the center).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility.equal_center_of_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility.equal_center_of_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A box consists of the nine points obtained by flipping one axis in each part of a three-plus-three split. The two splits use left parts {0,1,2} and {0,1,3}. On each box, the height is an offset plus the bit indicator of the flips from its center.

On a coordinate where two centers differ, the two height formulas have opposite slopes in that bit. Two overlap points with different bits give conflicting increments. Simultaneous XOR translation fixes the first center at zero, so the kernel checks only four pairs of split labels and sixty-four relative centers. The overlapping boxes then have the same center.

**Theorem 1.2 (A connected projection with threefold fibers has one split).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility.no_mixed_splits_of_connected_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility.no_mixed_splits_of_connected_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A path within boxes propagates the common center. Boxes in one slice are disjoint, so at most one can occur there since the two centered shapes have a common point. Each shape also has a point absent from the other. If both shapes occur, these two points each need three slices of their own shape, exceeding the four available slices.

This is the six-axis projection obstruction for the five-direction case in Hong, Wu and Xia's Problem 2. The statement assumes the disjoint box representation, common height, threefold fibers and projected connectivity. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility.equal_center_of_overlap`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility.no_mixed_splits_of_connected_projection`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/CubeBitMoves](../CoordinateHalves/CubeBitMoves.md)
