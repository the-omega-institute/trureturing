# Three-by-three rectangles in the nine-mask branch

## Abstract

The six-axis antipode aligns contacting slices as three-by-three rectangles.

**Theorem 1.1 (The six-axis antipode aligns the two slices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.aligned_layers_eq_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.aligned_layers_eq_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the antipode in the six active coordinates, the simultaneous translations act by corner swaps in the two parity blocks. The two aligned sets coincide and are a product.

**Theorem 1.2 (Both projections have three points).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.aligned_layer_three_by_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.aligned_layer_three_by_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared midpoint rule supplies exactly two neighbors in each candidate triple. The remaining antipodal point fixes the size of each projection at three.

**Theorem 1.3 (Every actual contact lies in a three-by-three rectangle).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.nine_masks_on_six_axes_force_contact_rectangles`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.nine_masks_on_six_axes_force_contact_rectangles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single coordinate permutation, obtained from the two parts of the mask graph, works for every distance-two contact on the chosen parity. In its exterior slice the six-axis antipode aligns both supports as the same three-by-three rectangle. This restricts the six-axis branch in Hong–Wu–Xia Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.aligned_layer_three_by_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.aligned_layers_eq_product`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer.nine_masks_on_six_axes_force_contact_rectangles`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit](Q9DegreeThreeContactOrbit.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ContactRectangles](Q9K33ContactRectangles.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph](Q9SquareMaskGraph.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridSignedCompression](../SixAxisGridSignedCompression.md)
