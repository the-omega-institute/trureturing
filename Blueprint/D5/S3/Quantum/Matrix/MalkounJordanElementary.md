# Malkoun's two-matrix elementary symmetric inequality

## Abstract

Elementary symmetric eigenvalue inequality for a Hermitian Jordan product.

**Definition 1.1 (The elementary symmetric polynomial).**

$$\forall (n: \mathbb{N}), \forall (t: Fin\left(n\right) \to \mathbb{R}), \forall (k: \mathbb{N}), elementarySymmetric\left(t, k\right) = \sum_{S\in \operatorname{Finset.powersetCard}\left(k, (\operatorname{Finset.univ}: Finset\left(Fin\left(n\right)\right))\right)}\prod_{i\in S}t\left(i\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/MalkounJordanElementary.elementarySymmetric` (`✓ std3`).

*Citation.* Malkoun (2026). *Promoting polynomial equalities for nonnegative variables to elementary symmetric polynomial inequalities*. URL: <https://mathoverflow.net/questions/512579>.

*Commentary.*

The kth elementary symmetric polynomial is the sum of products over all k-element subsets of Fin n. The entries are real; repeated values occupy distinct indices and retain their multiplicity.

**Definition 1.2 (The complete source assertion).**

$$claim = (\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (X: Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{C}\right)), \forall (Y: Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{C}\right)), \forall (hX: \operatorname{Matrix.PosSemidef}\left(X\right)), \forall (hY: \operatorname{Matrix.PosSemidef}\left(Y\right)), \forall (k: \mathbb{N}), (1 \le k) \Rightarrow ((k \le n) \Rightarrow (elementarySymmetric\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(jordan_{hermitian}\left(\operatorname{Matrix.PosSemidef.isHermitian}\left(hX\right), \operatorname{Matrix.PosSemidef.isHermitian}\left(hY\right)\right)\right), k\right) \le elementarySymmetric\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(\operatorname{Matrix.IsHermitian.add}\left(\operatorname{Matrix.IsHermitian.pow}\left(\operatorname{Matrix.PosSemidef.isHermitian}\left(hX\right), 2\right), \operatorname{Matrix.IsHermitian.pow}\left(\operatorname{Matrix.PosSemidef.isHermitian}\left(hY\right), 2\right)\right)\right), k\right)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/MalkounJordanElementary.claim` (`✓ std3`).

*Citation.* Malkoun (2026). *Promoting polynomial equalities for nonnegative variables to elementary symmetric polynomial inequalities*. URL: <https://mathoverflow.net/questions/512579>.

*Commentary.*

MathOverflow 512579, revision 1, displayed first question (unpaginated): for every positive n, every pair of complex n-by-n Hermitian positive semidefinite matrices X,Y, and every 1 ≤ k ≤ n, the kth elementary symmetric polynomial of the eigenvalues of XY+YX is at most that of X²+Y². Matrix.IsHermitian.eigenvalues lists the real eigenvalues with algebraic multiplicity, as certified by Mathlib's roots_charpoly_eq_eigenvalues. The positivity hypotheses concern X and Y. No positivity, invertibility, rank, simplicity of spectrum or small-order condition is imposed on XY+YX. The unspecified subsequent promotion question is outside this assertion.

**Theorem 1.3 (The elementary symmetric inequality).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MalkounJordanElementary.result` (`✓ std3`). ∎

*Resolves.* `Problems/malkoun-2026-mo512579-jordan-elementary` (proved) by `D5/S3/Quantum/Matrix/MalkounJordanElementary.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"malkoun-2026-mo512579-jordan-elementary","declaration_gid":"D5/S3/Quantum/Matrix/MalkounJordanElementary.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Malkoun (2026). *Promoting polynomial equalities for nonnegative variables to elementary symmetric polynomial inequalities*. URL: <https://mathoverflow.net/questions/512579>.

*Commentary.*

Fix a principal column set S. Stack the selected columns of X above those of Y to obtain U, and reverse the two blocks to obtain V. Hermiticity gives U*U=V*V=(X²+Y²)[S,S] and U*V=(XY+YX)[S,S]. The public frozen cauchyBinet declaration expands each determinant over the same ordered row subsets. Writing u and v for the resulting minor determinants, the real part of conjugate(u)v is at most half the sum of their squared moduli. Summing and using the equal Gram matrices proves the inequality of the real principal determinants. The characteristic-polynomial principal-minor identity and Hermitian spectral factorization identify the sum of these determinants with the original elementary symmetric polynomial. Summing the principal-minor inequalities proves the complete source assertion. All determinant identities are polynomial, so zero and singular matrices remain in scope. This is an application of existing Cauchy–Binet and spectral identities; no worldwide priority is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MalkounJordanElementary.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounJordanElementary.elementarySymmetric`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounJordanElementary.result`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../Schatten/CompoundMatrices.md)
