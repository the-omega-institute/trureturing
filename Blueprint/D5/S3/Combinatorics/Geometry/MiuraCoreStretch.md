# Arbitrarily long actual frozen runs

## Abstract

Arbitrarily long actual frozen runs.

**Definition 1.1 (Extend one genuine frozen run).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Insert immediately before a frozen column using its actual common signed slope.

**Theorem 1.2 (The extension reduces back exactly).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inserted column and the shifted original column form a genuine consecutive frozen pair. Deleting the inserted column returns the identical original array, giving a legal column-reduction step.

**Theorem 1.3 (Extension preserves the exact split and sides).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine frozen-run extension preserves the normalized residual predicate with the original exact minimum and maximum counts and the original common-side exclusion.

**Theorem 1.4 (Every extra run length has an actual realization).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.residual_frozen_run_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.residual_frozen_run_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From an actual residual array with a frozen column, every natural L gives a residual array with L extra columns, a legal deletion chain back to the original array, a remaining frozen column, and preservation of every originally frozen row.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.residual_frozen_run_extension`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn_reduction`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreStretch.stretchColumn_residual`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreJoint](MiuraCoreJoint.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreRestore](MiuraCoreRestore.md)
