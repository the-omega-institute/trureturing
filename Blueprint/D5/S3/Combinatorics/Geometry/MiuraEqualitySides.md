# MiuraEqualitySides

## Abstract

Actual-array geometric equality for the original Miura residual class.

**Theorem 1.1 (equality no neutral top minimum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_no_neutral_top_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_no_neutral_top_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one maximum row slab, a specified minimum row slab contains the physical first row, and a specified maximum row slab contains the physical last row, then both actual neutral slab families are empty. An extremum of the top profile in a neutral column interval would force a profile minimum there, hence an impermissible ambient minimum on a neutral support at the physical top. The first ambient maximum therefore lies in the bottom maximum slab and excludes every neutral row slab.

**Theorem 1.2 (equality two row types no neutral).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_two_row_types_no_neutral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_two_row_types_no_neutral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and exactly one maximum row slab, both actual neutral slab families are empty. The physical boundary slabs have opposite types; height negation handles the other top-boundary sign while preserving the same actual neutral intervals.

**Theorem 1.3 (equality two row types minima boundary).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_two_row_types_minima_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_two_row_types_minima_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and exactly one maximum row slab, then all ambient strict minima lie on the physical first row, or all lie on the physical last row. This is one common physical side for the whole minimum set. Saturation and the proved absence of neutral slabs place all minima in the single minimum slab, and the finite one-exit extrusion pushes them to that slab's physical boundary.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_no_neutral_top_minimum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_two_row_types_minima_boundary`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualitySides.equality_two_row_types_no_neutral`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed](MiuraEqualityCrossed.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral](MiuraEqualityNeutral.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityProfile](MiuraEqualityProfile.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation](MiuraEqualitySaturation.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabBudget](MiuraSlabBudget.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabSigns](MiuraSlabSigns.md)
