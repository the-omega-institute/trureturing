# The Negative-Determinant Square Obstruction

## Abstract

Determinant minus one prevents an integer matrix from being a matrix square.

**Theorem 1.1 (A determinant-minus-one integer matrix is not a square).**

$$\forall n, M\in\operatorname{Mat}_n(\mathbb{Z}), \operatorname{det}(M)=-1 \Rightarrow \neg \exists A\in\operatorname{Mat}_n(\mathbb{Z}), A^{2}=M$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Obstructions/NegativeDeterminantSquareObstruction.det_neg_one_not_matrix_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M were A squared, determinant multiplicativity would give det(M) = det(A)^2. An integer square is nonnegative, contradicting det(M) = -1. The argument works in every finite matrix dimension.

Repository search found concrete determinant-minus-one calculations but no general matrix-square obstruction. Pinned Mathlib text search and smart_search.sh found no exact theorem; the exact reusable declarations were Matrix.det_mul and mul_self_nonneg. An external GitHub-index search through Tavily likewise returned no exact declaration. The Lean proof therefore applies those two Mathlib results directly.

This closes only the determinant-minus-one obstruction sentence in residual remark 27.399-27.400. It does not claim that an odd word square is primitive, the balance formula, the trace divisibility statement, the census, or the zero-layer dimension bound stated elsewhere in the same atom.

## References

- Truth anchor: `D5/S3/PrimeForms/Obstructions/NegativeDeterminantSquareObstruction.det_neg_one_not_matrix_square`
