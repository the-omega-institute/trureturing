# The Odd-Core Trace-Square Identity

## Abstract

A determinant-minus-one integer matrix satisfies the odd-core trace-square identity.

**Theorem 1.1 (Determinant minus one fixes the trace of the square).**

$$\forall delta\in\operatorname{Mat}_{2}(\mathbb{Z}), \operatorname{det}(delta)=-1 \Rightarrow \operatorname{tr}(delta^{2})=\operatorname{tr}(delta)^{2}+2$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/OddCoreTraceSquare.trace_square_eq_of_det_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let delta be a 2x2 integer matrix with determinant -1. Then the trace of delta squared equals the square of the trace of delta plus two. This is the trace-square clause (c) of the odd-core theorem in residual E.38.

The proof expands the two diagonal entries of delta squared and substitutes the determinant hypothesis. It directly applies Mathlib declarations Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, and Fin.sum_univ_two; integer nonlinear arithmetic closes the resulting identity.

Repository and pinned-Mathlib searches found no existing declaration of this exact trace-square identity. Matrix.charpoly_fin_two provides the related two-dimensional characteristic-polynomial formula. This formalization does not claim the primitive-word, balance, pinned-divisibility, or dimension-bound clauses (a), (b), and (d) of E.38.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/OddCoreTraceSquare.trace_square_eq_of_det_neg_one`
