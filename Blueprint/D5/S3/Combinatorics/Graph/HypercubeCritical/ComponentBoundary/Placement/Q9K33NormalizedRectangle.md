# Coordinate normalization of both contact rectangles

## Abstract

Translating the missing labels fixes both rectangles and their contact axes.

**Theorem 1.1 (Normalize a contact rectangle and all its masks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle.normalization_of_nine_masks_on_six_axes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle.normalization_of_nine_masks_on_six_axes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the two parity triples has four labels and its rectangle occupies three. Translate the unique missing row and column and the exterior label to zero. In the normalized slice the left support has weight-two labels in both triples and the right support has weight-one labels in both. The same translation and permutation carry every contact on the chosen parity to one axis in each triple.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle.normalization_of_nine_masks_on_six_axes`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer](Q9K33AlignedLayer.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoNormalized](Q9TightDistanceTwoNormalized.md)
