# MiuraEqualitySaturation

## Abstract

Actual-array geometric equality for the original Miura residual class.

**Theorem 1.1 (equality nonneutral extremum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_nonneutral_extremum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_nonneutral_extremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid, with m at least two and n positive, assume that the individual-extremum count equals the neutral row-slab count plus the neutral column-slab count plus the product of the minimum row and column slab counts plus the product of the maximum row and column slab counts. Every individual extremum outside the union of the neutral row and column support sets lies either in a minimum row slab and a minimum column slab and is an ambient strict minimum, or in a maximum row slab and a maximum column slab and is an ambient strict maximum. Equality turns the existing matching-cell injection into a bijection, retaining each actual cell.

**Theorem 1.2 (equality slab extrema sign).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_slab_extrema_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_slab_extrema_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid, with m at least two and n positive, assume that the individual-extremum count equals the neutral row-slab count plus the neutral column-slab count plus the product of the minimum row and column slab counts plus the product of the maximum row and column slab counts. Every actual minimum-type row slab contains no ambient strict maximum, and every actual maximum-type row slab contains no ambient strict minimum. The two assertions quantify over every cell whose row lies in the specified slab.

**Theorem 1.3 (equality maximum slab unique).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_maximum_slab_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_maximum_slab_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid, with m at least two and n positive, assume that the individual-extremum count equals the neutral row-slab count plus the neutral column-slab count plus the product of the minimum row and column slab counts plus the product of the maximum row and column slab counts. If there is exactly one maximum column slab, each specified maximum row slab contains exactly one actual cell that is an ambient strict maximum.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_maximum_slab_unique`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_nonneutral_extremum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.equality_slab_extrema_sign`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabBudget](MiuraSlabBudget.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabClassification](MiuraSlabClassification.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabRunBound](MiuraSlabRunBound.md)
