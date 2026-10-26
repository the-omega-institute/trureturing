# Actual slab coverage

## Abstract

Every occupied row belongs to precisely one maximal occupied interval.

**Theorem 1.1 (An occupied row extends to an actual slab).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabCover.occupied_row_has_slab`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabCover.occupied_row_has_slab` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer array and every occupied row, there exists a maximal consecutive occupied interval containing that row. Choose a longest fully occupied interval containing it; an occupied immediately adjacent row would extend that interval and contradict maximality. No unit-edge assumption is needed for this finite interval fact.

**Theorem 1.2 (Exact and unique coverage).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabCover.row_slab_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabCover.row_slab_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A row of an actual integer array is occupied if and only if there is exactly one member of the canonical maximal occupied interval family containing it. Thus the interval families used in the incidence count are realized by the original height array and cover every extremum row.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabCover.occupied_row_has_slab`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabCover.row_slab_cover`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
