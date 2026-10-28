# Simultaneously reduced residual cores

## Abstract

Simultaneously reduced residual cores.

**Definition 1.1 (No consecutive frozen pair remains).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreNormal.NoAdjacentFrozen`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreNormal.NoAdjacentFrozen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column axis contains no consecutive pair of columns satisfying their genuine frozen equations. Applying the same predicate after transposition tests the row axis.

**Theorem 1.2 (A finite reduced core on both axes).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreNormal.residual_reduced_joint_core_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreNormal.residual_reduced_joint_core_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive exact extremum split and every actual residual rectangle with dimensions at least two, there is an actual related residual core with both dimensions between 2 and 2(a+b)-1, with no adjacent frozen pair on either axis. Reduction terminates because the sum of the dimensions decreases at every deletion. The conclusion establishes a reduced core, without identifying different reduction choices or their expansion fibers.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreNormal.NoAdjacentFrozen`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreNormal.residual_reduced_joint_core_exists`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreJoint](MiuraCoreJoint.md)
