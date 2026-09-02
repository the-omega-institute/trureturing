# Monomial Matrices Preserve Diagonality

## Abstract

Monomial matrices admit a diagonal-times-permutation form and preserve diagonality under the stated transpose sandwich.

**Definition 1.1 (Monomial matrix).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c: n \to R,\\\operatorname{monomial}\left(sigma, c\right) = \operatorname{Matrix}.\operatorname{of}\left(i, j \mapsto \begin{cases}c\left(i\right),&j = sigma\left(i\right)\\0,&\text{otherwise}\end{cases}\right).\end{gathered}$$

*Formalization.* `D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.monomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The monomial matrix attached to sigma and c places c(i) in row i at column sigma(i), and places zero at every other entry.

This is the generalized permutation matrix pattern with row scalars. When every scalar is nonzero, every row and column has one nonzero entry.

**Lemma 1.2 (Diagonal-times-permutation form).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c: n \to R,\\\operatorname{monomial}\left(sigma, c\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(c\right) \cdot \operatorname{PEquiv}.\operatorname{toMatrix}\left(\operatorname{Equiv}.\operatorname{toPEquiv}\left(sigma\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.monomial_eq_diagonal_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A monomial matrix is the permutation matrix of sigma multiplied on the left by the diagonal matrix of row scalars c.

**Theorem 1.3 (Diagonality after the transpose sandwich).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c, d: n \to R,\\{\operatorname{monomial}\left(sigma, c\right) \cdot \operatorname{Matrix}.\operatorname{diagonal}\left(d\right) \cdot \operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{monomial}\left(sigma, c\right)\right)}.\operatorname{IsDiag}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.isDiag_monomial_mul_diagonal_mul_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying a diagonal matrix on the left by a monomial matrix and on the right by its transpose permutes and rescales diagonal entries, so the resulting matrix remains diagonal.

No converse is proved or claimed: the theorem does not say that every matrix preserving diagonality must be monomial.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.isDiag_monomial_mul_diagonal_mul_transpose`
- Truth anchor: `D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.monomial`
- Truth anchor: `D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.monomial_eq_diagonal_mul`
