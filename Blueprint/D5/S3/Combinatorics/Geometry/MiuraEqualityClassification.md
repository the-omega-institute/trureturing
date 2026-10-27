# MiuraEqualityClassification

## Abstract

Actual-array geometric equality for the original Miura residual class.

**Theorem 1.1 (equality single side or four).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityClassification.equality_single_side_or_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityClassification.equality_single_side_or_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. Either all original minima lie on one common physical top, bottom, left or right side, as expressed by the original AllOnSide predicate on one-indexed integer cell coordinates and the exact minima finset, or there are exactly four individual extrema. The two-row-type result is applied to the same array or its actual transpose. Neither normalization nor a relation between minimum and maximum counts is required.

**Theorem 1.2 (residual frozen runs strict).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityClassification.residual_frozen_runs_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityClassification.residual_frozen_runs_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual m by n array h with both dimensions at least two, natural a,b,d with d at least five and a+b=d, suppose h satisfies the original Residual a b predicate: actual unit edges, normalization at the physical origin, the exact a minima and b maxima, and the complement of every single common physical minima side. If each actual axis has a genuinely unoccupied row, the sum of its actual frozen row-run count and frozen column-run count is at most d-1. The individual-extremum count is derived as d from the exact minimum and maximum counts; the general run bound and the single-side-or-four equality classification exclude equality. This closes the geometric strict-run obligation, while the whole polynomial counting claim remains a separate integration obligation.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityClassification.equality_single_side_or_four`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityClassification.residual_frozen_runs_strict`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualitySides](MiuraEqualitySides.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
