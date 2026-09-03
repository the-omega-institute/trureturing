# Transposes and Column Gram Matrices of Monomial Matrices

## Abstract

Transposes of monomial matrices and their column-side diagonal products.

**Theorem 1.1 (Transpose of a monomial matrix).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c: n \to R,\\\operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{monomial}\left(sigma, c\right)\right) = \operatorname{monomial}\left(sigma^{-1}, j \mapsto c\left(sigma^{-1}\left(j\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialColumnGram.monomial_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposing a monomial matrix gives a monomial matrix again, for the inverse permutation, with the scales relabelled along that inverse. This is the structural fact the module exists for.

**Theorem 1.2 (Column-side diagonal conjugation).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c, d: n \to R,\\\operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{monomial}\left(sigma, c\right)\right) \cdot \operatorname{Matrix}.\operatorname{diagonal}\left(d\right) \cdot \operatorname{monomial}\left(sigma, c\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(j \mapsto d\left(sigma^{-1}\left(j\right)\right) \cdot c\left(sigma^{-1}\left(j\right)\right)^2\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialColumnGram.transpose_mul_diagonal_mul_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The column-side conjugate is diagonal and is indexed by the inverse permutation: at j it is d at sigma inverse of j times the square of c at that same index.

This identity is derived from monomial_transpose together with the frozen row-side identity monomial_mul_diagonal_mul_transpose, not recomputed.

**Theorem 1.3 (Column Gram matrix of a monomial matrix).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c: n \to R,\\\operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{monomial}\left(sigma, c\right)\right) \cdot \operatorname{monomial}\left(sigma, c\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(j \mapsto c\left(sigma^{-1}\left(j\right)\right)^2\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialColumnGram.transpose_mul_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking d = 1 gives the column Gram matrix, whose diagonal at j is the square of the scale relabelled by the inverse permutation.

Nothing is asserted about unitary groups, spectra, eigenvalues, or any converse.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MonomialColumnGram.monomial_transpose`
- Truth anchor: `D5/S3/Quantum/Matrix/MonomialColumnGram.transpose_mul_diagonal_mul_monomial`
- Truth anchor: `D5/S3/Quantum/Matrix/MonomialColumnGram.transpose_mul_monomial`
- Dependency: [D5/S3/Quantum/Matrix/MonomialGram](MonomialGram.md)
