# Affine Lines over a Finite Field

## Abstract

Finite-field affine lines through a point are indexed by slopes and one vertical direction.

**Theorem 1.1 (A point lies on field-cardinality plus one affine lines).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.card_affineLines_through`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.card_affineLines_through` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field F and a point p in F x F, the graph lines y = m x + b are indexed by m in F, and one additional vertical line x = p.1 passes through p. The resulting finite set has cardinality Fintype.card F + 1.

**Theorem 1.2 (Two distinct points determine one affine line).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.exists_unique_line_through_distinct_points`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.exists_unique_line_through_distinct_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct points, equal first coordinates force the unique vertical line; unequal first coordinates determine the unique slope and intercept by field division. The Lean proof covers both cases explicitly.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.card_affineLines_through`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.exists_unique_line_through_distinct_points`
