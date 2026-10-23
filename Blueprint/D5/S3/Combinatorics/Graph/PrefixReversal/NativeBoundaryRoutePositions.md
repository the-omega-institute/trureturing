# Locate the Actual Zero Left Port in Native Routes

## Abstract

Locate the Actual Zero Left Port in Native Routes.

**Theorem 1.1 (The Even Route Has Its Zero Left Port at the Exact Index).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.native_even_left_zero_piece_position`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.native_even_left_zero_piece_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual ordered special-child pieces whose finishes follow the even native route at order 2s+2, native port injectivity identifies the unique piece finishing at the zero left port. Its index is exactly s+1, so it comes after the first rooted boundary piece.

**Theorem 1.2 (The Odd Route Includes the Empty Ladder Case).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.native_odd_left_zero_piece_position`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.native_odd_left_zero_piece_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual ordered special-child pieces whose finishes follow the odd native route at order 2s+3, the zero left port occurs precisely at index s+1. This exact statement includes order three and supplies the later-cut position used by literal Q slicing.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.native_even_left_zero_piece_position`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.native_odd_left_zero_piece_position`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances](NativeSpecialBoundaryInstances.md)
