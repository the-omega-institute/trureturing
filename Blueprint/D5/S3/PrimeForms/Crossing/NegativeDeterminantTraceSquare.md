# The Trace Square at Determinant Minus One

## Abstract

A 2x2 integer matrix of determinant -1 has trace of its square equal to trace squared plus two.

**Theorem 1.1 (Determinant minus one fixes the trace of the square).**

$$\forall A\in\operatorname{Mat}_{2}(\mathbb{Z}), \operatorname{det}(A)=-1 \Rightarrow \operatorname{tr}(A^{2})=\operatorname{tr}(A)^{2}+2$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/NegativeDeterminantTraceSquare.trace_square_of_det_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a 2x2 matrix A, direct expansion gives tr(A^2) = tr(A)^2 - 2 det(A). The determinant hypothesis det(A) = -1 therefore gives tr(A^2) = tr(A)^2 + 2.

Pinned Mathlib and repository searches found no exact trace-square theorem. The proof imports and applies Mathlib's Matrix.trace_fin_two and Matrix.det_fin_two expansions, expands the two-entry matrix products, and closes the resulting integer polynomial identity with ring.

This formalizes only clause (c) of residual E.38: the trace identity forced by determinant -1. It does not assert the word-primitivity criterion, balance, the square-city parameter formula, divisibility by 12, the census, or the zero-layer dimension bound stated elsewhere in that atom.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/NegativeDeterminantTraceSquare.trace_square_of_det_neg_one`
