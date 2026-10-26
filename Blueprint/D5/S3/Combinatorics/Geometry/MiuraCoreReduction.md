# Finite one-axis core reduction

## Abstract

Bounded-width reduction follows the original actual array.

**Definition 1.1 (A chain of actual signed deletions).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreReduction.ColumnReduction`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreReduction.ColumnReduction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reflexive relation starts at the given array. Each further step deletes one of two consecutive genuinely frozen columns using its actual signed slope. The target of that deletion is exactly the source of the remaining chain.

**Theorem 1.2 (A bounded-width residual from the same array).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreReduction.residual_column_core_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreReduction.residual_column_core_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive split a,b, nonempty row axis, and residual array with at least two columns, there is an actual residual array of width between 2 and 2(a+b)-1 connected to it by a finite chain of signed frozen deletions. Strong induction on width applies the consecutive-frozen-column bound and the exact residual-preservation theorem at every step. This establishes existence of a related bounded-width array; uniqueness of a reduced core and the joint expansion fibers require further arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreReduction.ColumnReduction`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreReduction.residual_column_core_exists`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreResidual](MiuraCoreResidual.md)
