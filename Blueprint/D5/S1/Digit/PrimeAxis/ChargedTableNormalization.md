# Charged Table Normalization

## Abstract

Charged Table Normalization.

**Theorem 1.1 (A finite sequence normalizes the entire table).**

Lean statement: `D5/S1/Digit/PrimeAxis/ChargedTableNormalization.exists_tablePath_rowNormalize`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/ChargedTableNormalization.exists_tablePath_rowNormalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finitely supported prime-indexed raw table reaches its rowwise normal form by one finite sequence of single-row carry steps. Each step acts on one prime row and leaves every other row unchanged. The charge is a finitely supported prime-indexed integer function, obtained by adding each step's charge at its selected prime. Empty tables and empty paths are included.

**Theorem 1.2 (Projection preserves the charge at each prime).**

Lean statement: `D5/S1/Digit/PrimeAxis/ChargedTableNormalization.tablePath_project`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/ChargedTableNormalization.tablePath_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite table path and every prime, the source row reduces to the endpoint row by a finite charged raw carry path. Its total charge is exactly the table path's charge at that prime. Steps acting on another row leave both this row and its accumulated charge unchanged.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxis/ChargedTableNormalization.exists_tablePath_rowNormalize`
- Truth anchor: `D5/S1/Digit/PrimeAxis/ChargedTableNormalization.tablePath_project`
- Dependency: [D5/S1/Deficit/ChargedCarryPath](../../Deficit/ChargedCarryPath.md)
- Dependency: [D5/S1/Digit/PrimeAxisTable](../PrimeAxisTable.md)
