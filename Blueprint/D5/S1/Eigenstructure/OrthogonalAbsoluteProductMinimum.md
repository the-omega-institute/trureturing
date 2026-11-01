# Orthogonal Absolute-Product Minimum

## Abstract

Every nonsingular real square matrix has orthogonal absolute-product minimum exactly one, attained by a Gram-Schmidt basis.

Source: User3 (MathOverflow user 600125), A nontrivial lower bound for the orthogonally transformed absolute product, MathOverflow question 515549, https://mathoverflow.net/questions/515549, revision 1 CB719581-BCE3-4573-931E-15327002F861, published 2026-09-25T19:17:56+00:00, CC BY-SA 4.0. The source asks whether a bound beta(P)>1 can hold for every orthogonal Q for a class of nonsingular P, and asks to characterize the infimum. The theorem below characterizes that value as the attained constant one. The derivation is an application of the cited library results; no claim of worldwide novelty or all-minimizer classification is made.

**Definition 1.1 (Entrywise absolute value).**

Lean statement: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.entryAbs`

*Formalization.* `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.entryAbs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural K and real K-by-K matrix A, entryAbs(A) has entry (i,j) equal to the real absolute value of A(i,j). This operation does not denote a matrix norm or the positive square root of a matrix product.

**Definition 1.2 (Complex spectral radius of a real matrix).**

Lean statement: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.radius`

*Formalization.* `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.radius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural K and real K-by-K matrix A, radius(A) is the complex spectral radius after entrywise inclusion of the real entries into the complex numbers. Lean's spectralRadius has extended nonnegative real values; toReal converts it to a real number. Finite matrices have finite spectral radius, by spectrum.spectralRadius_le_nnnorm, so this conversion retains the usual spectral radius. For positive K it is the maximum modulus of the complex eigenvalues, including multiplicity only insofar as it determines the spectrum.

**Definition 1.3 (The full real orthogonal domain).**

Lean statement: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.Orthogonal`

*Formalization.* `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.Orthogonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural K, Orthogonal(Q) asserts both transpose(Q) times Q equals the identity and Q times transpose(Q) equals the identity. All products are ordinary square-matrix products.

**Definition 1.4 (The source objective).**

$$\forall K \in \mathbb{N}, \forall P,Q \in \mathbb{R}^{K \times K},\ \operatorname{objective}\left(P, Q\right) = \operatorname{rho}\left(\left|PQ\right| \left|Q^{T} P^{-1}\right|\right)$$

*Formalization.* `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.objective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural K and real K-by-K matrices P and Q, the objective is the complex spectral radius of entryAbs(PQ) times entryAbs(transpose(Q) times inverse(P)). Inverse is the ordinary matrix inverse when det(P) is nonzero; the result uses exactly that nonsingular domain.

**Theorem 1.5 (Universal lower bound and an attaining orthogonal matrix).**

$$\forall K \in \mathbb{N}, K > 0,\ \forall P \in \mathbb{R}^{K \times K}, \operatorname{det}\left(P\right) \neq 0 \Rightarrow\ (\forall Q \in \operatorname{O}\left(K\right), \operatorname{objective}\left(P, Q\right) \ge 1) \land\ (\exists Q \in \operatorname{O}\left(K\right), \operatorname{objective}\left(P, Q\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/user3-2026-orthogonal-absolute-product-minimum` (proved) by `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"user3-2026-orthogonal-absolute-product-minimum","declaration_gid":"D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every positive integer K and every real K-by-K matrix P with nonzero determinant, every orthogonal Q has objective at least one, and there exists an orthogonal Q with objective exactly one. No upper bound on dimension, matrix sign condition, approximation, norm substitute or diagonalizability hypothesis is imposed. The existence clause is an actual attained equality, not only an infimum statement.

For arbitrary orthogonal Q, set A=PQ and B=transpose(Q) times inverse(P). Their product is the identity. The finite-sum triangle inequality gives identity <= entryAbs(A) entryAbs(B) entrywise. D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_mono compares their spectral radii and gives the universal bound.

Apply InnerProductSpace.gramSchmidtOrthonormalBasis to the ordered rows of P in real Euclidean K-space, and place this orthonormal basis in the columns of Q. Mathlib's basis-change identities give both orthogonality equations. Its gramSchmidtOrthonormalBasis_inv_triangular theorem makes T=PQ lower triangular. Nonsingularity and orthogonality identify inverse(T) with transpose(Q) times inverse(P). Matrix.blockTriangular_inv_of_blockTriangular gives the same triangular orientation for that inverse.

The absolute values retain the triangular zeros. In a diagonal entry of a product of two lower triangular matrices, only the matching diagonal term survives. Since T times inverse(T) is the identity, each diagonal entry of entryAbs(T) entryAbs(inverse(T)) is one. The product remains lower triangular. After complexification, transpose and Matrix.charpoly_of_isUpperTriangular give characteristic polynomial (X-1)^K. Matrix.mem_spectrum_iff_isRoot_charpoly and K>0 identify the spectrum with the singleton {1}; spectralRadius_eq_of_unital gives radius one, without any diagonalizability assumption.

Consequently the minimum, and hence the infimum, of the source objective over the entire orthogonal group is one. A strict lower bound beta(P)>1 uniform over that group is impossible for any nonsingular P, and therefore for any nonempty class of them. These are mathematical consequences of the displayed two-clause theorem; no separate companion result is introduced.

## References

- Truth anchor: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.Orthogonal`
- Truth anchor: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.entryAbs`
- Truth anchor: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.objective`
- Truth anchor: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.radius`
- Truth anchor: `D5/S1/Eigenstructure/OrthogonalAbsoluteProductMinimum.result`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookOrder](../Digit/Infinite/ResetCodebookOrder.md)
