# Actual slab coverage

## Abstract

Every occupied row extends to a maximal occupied interval.

**Theorem 1.1 (An occupied row extends to an actual slab).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabCover.occupied_row_has_slab`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabCover.occupied_row_has_slab` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer array and every occupied row, there exists a maximal consecutive occupied interval containing that row. Choose a longest fully occupied interval containing it; an occupied immediately adjacent row would extend that interval and contradict maximality. No unit-edge assumption is needed for this finite interval fact.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabCover.occupied_row_has_slab`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
