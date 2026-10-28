# Exact residual transport under axis exchange

## Abstract

Exact residual transport under axis exchange.

**Theorem 1.1 (Each extremum sign is counted separately).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_extremum_cards`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_extremum_cards` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate swap bijects strict minima with strict minima and strict maxima with strict maxima, using every existing neighbour in both grids.

**Definition 1.2 (Physical sides follow the axes).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transposeSide`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transposeSide` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Top and bottom exchange with left and right under transposition.

**Theorem 1.3 (The common side is transported exactly).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_all_minima_side_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_all_minima_side_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each specified physical side of the transposed rectangle, all minima lie on that side exactly when all original minima lie on its exchanged side.

**Theorem 1.4 (The original residual predicate is preserved).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposition preserves the unit-edge law, origin normalization, the exact minimum and maximum counts separately, and failure of containment of all minima in any single physical side.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transposeSide`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_all_minima_side_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_extremum_cards`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.transpose_residual`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreReduction](MiuraCoreReduction.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
