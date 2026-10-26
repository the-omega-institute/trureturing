# Commuting contractions on one actual rectangle

## Abstract

Commuting contractions on one actual rectangle.

**Definition 1.1 (Signed deletion along the row axis).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contractRow`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contractRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row contraction is column contraction of the actual transpose followed by transposition back.

**Theorem 1.2 (A frozen row remains legal).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.frozen_row_after_column`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.frozen_row_after_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting one common column slope from each cell to the right of the deleted column preserves the frozen-row second-difference equations at every surviving column.

**Theorem 1.3 (A frozen column remains legal).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.frozen_column_after_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.frozen_column_after_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same preservation law with exchanged axes retains each original frozen column after row contraction.

**Theorem 1.4 (The two deletion orders agree exactly).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contract_row_column_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contract_row_column_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual row and column satisfying their frozen equations, both successive signed contractions are legal and yield equal integer-valued functions on the same smaller rectangle. The origin-adjacent slope of either operation is unchanged by the other operation; the two corrections add.

**Theorem 1.5 (Row contraction preserves the residual class).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contractRow_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contractRow_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A legal signed row deletion preserves normalization, each exact extremum count, and the predicate that the minima are contained in no single common physical side.

**Definition 1.6 (Chains on successive actual arrays).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.JointReduction`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.JointReduction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each column or row step deletes one of two consecutive genuinely frozen lines. Its output is the actual input of the remaining chain.

**Theorem 1.7 (Both finite bounds hold on one residual array).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.residual_joint_bounded_core_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.residual_joint_bounded_core_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, a residual array on a rectangle with at least two cells per axis admits an actual joint deletion chain to a residual array with each dimension between 2 and 2(a+b)-1. Column reduction followed by transposed column reduction gives the same bounded target object. This is an existence result and does not assert uniqueness.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.JointReduction`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contractRow`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contractRow_residual`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.contract_row_column_commute`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.frozen_column_after_row`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.frozen_row_after_column`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreJoint.residual_joint_bounded_core_exists`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreTranspose](MiuraCoreTranspose.md)
