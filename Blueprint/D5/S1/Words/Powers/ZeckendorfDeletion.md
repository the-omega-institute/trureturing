# Literal Zeckendorf deletion

## Abstract

Deleting the least significant Fibonacci position recovers the index of the containing golden substitution block.

**Definition 1.1 (Delete a position and decode).**

Lean statement: `D5/S1/Words/Powers/ZeckendorfDeletion.deleteLeast`

*Formalization.* `D5/S1/Words/Powers/ZeckendorfDeletion.deleteLeast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the canonical occupied Fibonacci indices, whose weights start at F_2=1 and F_3=2. Remove index 2, subtract one from each remaining index, and sum the resulting Fibonacci weights. Removing the position is different from retaining its weight as F_1. This is the literal operation defining OEIS A319433, with its original index including zero.

**Theorem 1.2 (The block containing an index).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{goldenSubstStart}\left(\operatorname{deleteLeast}\left(n\right)\right) \le n) \land (n < \operatorname{goldenSubstStart}\left(\operatorname{deleteLeast}\left(n\right) + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/ZeckendorfDeletion.deletion_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A block start shifts all canonical occupied indices upward by one, so deletion recovers its source index. A second position exists exactly when the source has no occupied index 2. Its canonical digits append index 2 to the shifted list, and deletion removes precisely that appended digit. The existing substitution blocks cover every natural index, establishing both interval inequalities without defining deletion by a floor formula.

## References

- Truth anchor: `D5/S1/Words/Powers/ZeckendorfDeletion.deleteLeast`
- Truth anchor: `D5/S1/Words/Powers/ZeckendorfDeletion.deletion_block`
- Dependency: [D5/S1/Digit/GoldenBase4DenseInput](../../Digit/GoldenBase4DenseInput.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf](GoldenDesubstitutionZeckendorf.md)
