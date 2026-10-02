# Legal residual normal forms

## Abstract

Legal residual normal forms.

**Definition 1.1 (Fixed-length binary rank).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualNormalForm.rank`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualNormalForm.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rank [] = 0 and rank (a :: w) = a.val * 2 ^ w.length + rank w for words over Fin 2. At fixed length this natural-number rank strictly decreases when B1 is replaced by B0.

**Theorem 1.2 (Legal residual normal forms).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualNormalForm.normalized_state_cover`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfResidualNormalForm.normalized_state_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem normalized_state_cover (H : ℕ) (hH : 14 ≤ H) (w : List (Fin 2)) (hw : NoAdjacentOnes w) : ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧ ZeckendorfRawWindow.residual (Nat.fib H) w = ZeckendorfRawWindow.residual (Nat.fib H) v ∧ ¬ B1 <:+: v.drop 7`.

Every complete F_H residual has a legal length H+7 representative whose final H digits avoid 00010101001000. Arbitrary-context replacement preserves the complete residual and strictly decreases fixed-length binary rank; no confluence assumption is required.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfResidualNormalForm.normalized_state_cover`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualNormalForm.rank`
- Dependency: [D5/S1/Digit/ZeckendorfContextualReplacement](ZeckendorfContextualReplacement.md)
- Dependency: [D5/S1/Digit/ZeckendorfResidualCover](ZeckendorfResidualCover.md)
