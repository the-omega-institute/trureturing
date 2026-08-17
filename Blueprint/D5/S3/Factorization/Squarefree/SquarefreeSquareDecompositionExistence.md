# Existence and Uniqueness of the Square-Squarefree Decomposition

## Abstract

Every positive natural number is uniquely a square times a squarefree number.

**Theorem 1.1 (Positive naturals have a unique square-squarefree decomposition).**

$$\forall n \in \mathbb{N},\ n > 0 \Rightarrow \exists! (b, a) \in \mathbb{N} \times \mathbb{N},\ b > 0 \land \operatorname{Squarefree}(a) \land b^{2} \cdot a = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Squarefree/SquarefreeSquareDecompositionExistence.bcs_square_squarefree_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive natural n there is exactly one ordered pair (b, a) of natural numbers such that b is positive, a is squarefree, and b^2 * a = n. The ordering records the square root first and the squarefree part second.

The proof reuses both available library results. Pinned Mathlib supplies the existence of a positive square-times-squarefree decomposition through Nat.sq_mul_squarefree_of_pos. The repository's existing theorem bcs_square_squarefree_unique proves that any two such decompositions agree. Combining them yields existence and uniqueness without reproving either half.

This closes only the first assertion of residual remark 27.326: the BCS decomposition of positive naturals. It makes no claim about the k-free ladder, zeta identities, Mobius sums, Mertens behavior, or the Riemann hypothesis language that also appears in the source atom.

## References

- Truth anchor: `D5/S3/Factorization/Squarefree/SquarefreeSquareDecompositionExistence.bcs_square_squarefree_exists_unique`
- Dependency: [D5/S3/Factorization/SquarefreeSquareDecomposition](../SquarefreeSquareDecomposition.md)
