# Explicit inverse signed insertion

## Abstract

Explicit inverse signed insertion.

**Definition 1.1 (Insert the translated preceding profile).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an internal column coordinate j, retain earlier columns and translate the profile at column x-1 by the signed step s for each x at or after j. The inserted column uses the preceding profile.

**Theorem 1.2 (Every unit edge survives insertion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_isHeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_isHeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the original function has unit absolute differences on grid edges and s is either 1 or -1, every vertical and horizontal edge of the inserted array again has unit absolute difference. The new seam contributes exactly s.

**Definition 1.3 (The actual signed seam condition).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.SeamSlope`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.SeamSlope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every row, the difference between the original columns j and j-1 equals the same integer s. This condition is local to the actual insertion seam.

**Theorem 1.4 (The inserted column is frozen).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_frozen`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_frozen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common signed seam equation makes the inserted profile the midpoint of its two neighbouring profiles, so the inserted column satisfies the genuine frozen equations.

**Theorem 1.5 (Contraction inverts insertion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.contractAt_restoreColumn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.contractAt_restoreColumn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty row axis and an internal insertion coordinate satisfying the signed seam condition, contracting the inserted frozen column recovers the identical original function.

**Theorem 1.6 (Insertion inverts contraction).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_contractAt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_contractAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given an actual unit-edge function and one of its genuinely frozen columns, insert its actual common signed slope into the contracted function. Every original cell value, including the deleted column, is recovered exactly.

**Theorem 1.7 (The exact residual predicate survives insertion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive or negative unit seam insertion into a normalized residual array preserves each minimum and maximum count separately and preserves the failure of all minima to lie on a single common physical side. The seam condition and the unit-edge law are verified on that same array.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.SeamSlope`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.contractAt_restoreColumn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_contractAt`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_frozen`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_isHeight`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreRestore.restoreColumn_residual`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreNormal](MiuraCoreNormal.md)
