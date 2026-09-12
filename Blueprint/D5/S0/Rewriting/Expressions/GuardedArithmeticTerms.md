# Guarded finite arithmetic terms

## Abstract

Guarded finite arithmetic terms.

Typed Lean handles carry these statements. Formula projection limitations are reported by the canonical Scribe tools; no handwritten formula substitutes for a Lean type. The actual real interpretation and the full shared-world expression theorem remain E2.

**Definition 1.1 (The object language is Mathlib finite term syntax).**

Lean statement: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.Expr`

*Formalization.* `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.Expr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constants and variables occupy different sum leaves. The arithmetic signature has exactly unary negation and binary addition, multiplication and division. Ordered term children retain parentheses. Temporal composition, spatial filters and history queries have no symbols.

**Theorem 1.2 (Division legality requires both children and its guard).**

Lean statement: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.allLegal_div`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.allLegal_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A division term is structurally legal exactly when both children are structurally legal and their actual evaluation results satisfy the algebra guard. The existential witnesses are those two child results.

**Theorem 1.3 (Existence is exactly structural legality).**

Lean statement: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.legal_iff_allLegal`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.legal_iff_allLegal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AllLegal recursively requires every child and the guard at every division node. Multiplication by a numerical zero and cancellation do not erase an illegal subexpression.

**Theorem 1.4 (Proved operation maps commute with finite realization).**

Lean statement: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.eval_map`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.eval_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a conditional generic transport theorem. mapHom constructs a first-order homomorphism after the primitive operation and guard laws have been supplied as proofs. HomClass.realize_term supplies the finite-term transport. Algebra itself contains only operation data. The integer and rational consumers prove every native premise.

## References

- Truth anchor: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.Expr`
- Truth anchor: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.allLegal_div`
- Truth anchor: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.eval_map`
- Truth anchor: `D5/S0/Rewriting/Expressions/GuardedArithmeticTerms.legal_iff_allLegal`
