# The six-axis nine-mask case in a 258-point candidate

## Abstract

The six-axis contact rectangles force a component smaller than sixty.

**Theorem 1.1 (The six-axis nine-mask case is impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportReplay.no_nine_masks_on_six_axes_in_actual_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportReplay.no_nine_masks_on_six_axes_in_actual_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized rectangles and the local degree and parity equations constrain the two actual components. Two-coordinate spectral saturation supplies the corner witnesses. The refutation uses seven clauses requiring an occupied vertex outside specified supports of size fifty-four. Each clause follows from the ambient bound of sixty. Lean checks the clause meanings and replays the resolution certificate. This removes the six-axis branch of Hong–Wu–Xia Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportReplay.no_nine_masks_on_six_axes_in_actual_pair`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs](Q9K33CompletionInputs.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle](Q9K33NormalizedRectangle.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches](Q9K33ReplayBatches.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses](Q9K33SmallSupportClauses.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay](Q9SharedContactGeometryReplay.md)
