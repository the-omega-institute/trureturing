# Both extrema in a neutral slab

## Abstract

Neutral occupied strips contain both signs of actual ambient extrema.

**Definition 1.1 (Occupied rows).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.RowOccupied`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.RowOccupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row is occupied precisely when some cell in it is a strict local minimum or maximum of the full grid, with every existing neighbour included.

**Definition 1.2 (Equal signed cuts).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.EqualRowCuts`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.EqualRowCuts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interval is internal, and its entire top and bottom cuts have the same specified downward height increment. These are actual edges of the same height function.

**Theorem 1.3 (Both signs of ambient extrema).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.neutral_row_has_both`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.neutral_row_has_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-edge integer height array, if a nonempty internal row interval contains an occupied row and both boundary cuts have the same unit slope, the interval contains an ambient minimum and an ambient maximum. The statement includes both slope signs. One-exit rigidity excludes the absence of a maximum for increasing cuts. Reflection together with height negation gives a minimum, and negation covers decreasing cuts.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.EqualRowCuts`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.RowOccupied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabNeutral.neutral_row_has_both`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabExtrema](MiuraSlabExtrema.md)
