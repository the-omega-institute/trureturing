# Gram Matrices of Monomial Matrices

## Abstract

Exact diagonals obtained from monomial matrices and their transposes.

**Theorem 1.1 (Diagonal conjugation by a monomial matrix).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c, d: n \to R,\\\operatorname{monomial}\left(sigma, c\right) \cdot \operatorname{Matrix}.\operatorname{diagonal}\left(d\right) \cdot \operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{monomial}\left(sigma, c\right)\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(i \mapsto d\left(sigma\left(i\right)\right) \cdot c\left(i\right)^2\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialGram.monomial_mul_diagonal_mul_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating a diagonal matrix by a monomial matrix gives a diagonal matrix whose entry at i is the weight read at the permuted index sigma(i), times the square of the row scale c(i).

No mixing occurs because a monomial matrix has at most one nonzero entry per row: a surviving term needs the same column index for two rows, which forces the rows equal because sigma is injective.

The frozen isDiag_monomial_mul_diagonal_mul_transpose asserts only that this conjugate is diagonal, a property with no entry values; this module sharpens that to the exact diagonal, while the frozen statement is neither restated nor amended.

**Theorem 1.2 (Gram matrix of a monomial matrix).**

$$\begin{gathered}\forall n: Type, [\operatorname{DecidableEq}\left(n\right)], [\operatorname{Fintype}\left(n\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall sigma: \operatorname{Equiv}.\operatorname{Perm}\left(n\right), c: n \to R,\\\operatorname{monomial}\left(sigma, c\right) \cdot \operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{monomial}\left(sigma, c\right)\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(i \mapsto c\left(i\right)^2\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MonomialGram.monomial_mul_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking d = 1 gives the Gram matrix of the monomial matrix itself: its diagonal entries are the squares of the row scales.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MonomialGram.monomial_mul_diagonal_mul_transpose`
- Truth anchor: `D5/S3/Quantum/Matrix/MonomialGram.monomial_mul_transpose`
- Dependency: [D5/S3/Quantum/Matrix/MonomialDiagonalPreserving](MonomialDiagonalPreserving.md)
