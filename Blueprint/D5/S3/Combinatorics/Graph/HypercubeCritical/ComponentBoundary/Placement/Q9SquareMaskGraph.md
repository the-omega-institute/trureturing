# The mask graph of a distance-two component pair

## Abstract

Forced squares constrain the number and shape of distance-two contact masks.

**Theorem 1.1 (Minimum degree and square completion).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.distance_two_mask_graph_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.distance_two_mask_graph_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For separated connected balanced cubic components with universally singular signed defect, the mask graph has minimum degree three and square completion along edges between cubic vertices.

**Theorem 1.2 (Seven axes exclude eleven masks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.no_eleven_masks_on_seven_axes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.no_eleven_masks_on_seven_axes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eleven edges on seven axes with minimum degree three would leave a unique degree-four vertex. Square completion rules out this graph.

**Theorem 1.3 (Nine masks on six axes force K3,3).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.nine_masks_on_six_axes_bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.nine_masks_on_six_axes_bipartite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nine edges on six axes make the mask graph cubic. Square completion then forces the complete bipartite graph with two three-axis parts.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.distance_two_mask_graph_constraints`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.nine_masks_on_six_axes_bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph.no_eleven_masks_on_seven_axes`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit](Q9DegreeThreeContactOrbit.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph](Q9EightMaskGraph.md)
