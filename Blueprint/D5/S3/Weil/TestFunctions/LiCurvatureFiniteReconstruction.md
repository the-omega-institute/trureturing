# Finite Li Curvature Reconstruction

## Abstract

Normalized Hermitian second differences reconstruct finite Toeplitz quadratic forms, with a smallest-eigenvalue obstruction and a two-point absolute growth bound.

Throughout, T(c,n) has row and column indices in Fin(n), and e(n) is the complex all-ones vector on the same type. Both indices are cast to integers before subtraction.

$$
\operatorname{T}\left(c, n, j, k\right) = \operatorname{c}\left(\operatorname{Int}\left(j\right) - \operatorname{Int}\left(k\right)\right)
$$

$$
\operatorname{e}\left(n, j\right) = 1
$$

Ico(1,n) is the natural interval from one inclusive to n exclusive. Real and Int in the formulas denote casts; NatSub is truncated natural subtraction. For positive n, last(n) is the element of Fin(card(Fin(n))) with value n minus one. The eigenvaluesZero enumeration is Mathlib's descending eigenvalues enumeration.

**Theorem 1.1 (Weighted curvature reconstruction).**

$$\forall u \in \mathbb{N}\to\mathbb{R},\; \forall L \in \mathbb{R},\; \forall c \in \mathbb{Z}\to\mathbb{C},\; \operatorname{u}\left(0\right) = 0 \Rightarrow \left(\operatorname{u}\left(1\right) = L \Rightarrow \left(0 \le L \Rightarrow \left(\operatorname{c}\left(0\right) = 1 \Rightarrow \left(\left(\forall k \in \mathbb{Z},\; \operatorname{c}\left(0 - k\right) = \operatorname{star}\left(\operatorname{c}\left(k\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{u}\left(n + 1\right) - 2 \cdot \operatorname{u}\left(n\right) + \operatorname{u}\left(\operatorname{NatSub}\left(n, 1\right)\right) = 2 \cdot L \cdot \operatorname{re}\left(\operatorname{c}\left(\operatorname{Int}\left(n\right)\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{u}\left(n\right) = L \cdot \left(\operatorname{Real}\left(n\right) + 2 \cdot \sum_{k\in \operatorname{Ico}\left(1, n\right)} {\left(\operatorname{Real}\left(n\right) - \operatorname{Real}\left(k\right)\right) \cdot \operatorname{re}\left(\operatorname{c}\left(\operatorname{Int}\left(k\right)\right)\right)}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.recurrence_eq_weighted_curvature_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository's second_difference_recurrence_unique is applied to the displayed candidate sequence. Mathlib's finite interval extension identities verify its initial values and second differences. This is the finite algebraic reconstruction, including zero and one and without division by L.

**Theorem 1.2 (Signed finite diagonal count).**

$$\forall c \in \mathbb{Z}\to\mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{e}\left(n\right)\right), \operatorname{mulVec}\left(\operatorname{T}\left(c, n\right), \operatorname{e}\left(n\right)\right)\right) = \operatorname{Complex}\left(n\right) \cdot \operatorname{c}\left(0\right) + \sum_{k\in \operatorname{Ico}\left(1, n\right)} {\left(\operatorname{Complex}\left(n\right) - \operatorname{Complex}\left(k\right)\right) \cdot \left(\operatorname{c}\left(\operatorname{Int}\left(k\right)\right) + \operatorname{c}\left(0 - \operatorname{Int}\left(k\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.toeplitz_ones_diagonal_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's interval Fubini and reflection identities split the square into its diagonal and two strict triangles. Each signed gap has n minus k entries. The identity requires neither Hermitian symmetry nor normalization, and retains both complex coefficients before taking real parts.

**Theorem 1.3 (The actual size-n quadratic form).**

$$\forall u \in \mathbb{N}\to\mathbb{R},\; \forall L \in \mathbb{R},\; \forall c \in \mathbb{Z}\to\mathbb{C},\; \operatorname{u}\left(0\right) = 0 \Rightarrow \left(\operatorname{u}\left(1\right) = L \Rightarrow \left(0 \le L \Rightarrow \left(\operatorname{c}\left(0\right) = 1 \Rightarrow \left(\left(\forall k \in \mathbb{Z},\; \operatorname{c}\left(0 - k\right) = \operatorname{star}\left(\operatorname{c}\left(k\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{u}\left(n + 1\right) - 2 \cdot \operatorname{u}\left(n\right) + \operatorname{u}\left(\operatorname{NatSub}\left(n, 1\right)\right) = 2 \cdot L \cdot \operatorname{re}\left(\operatorname{c}\left(\operatorname{Int}\left(n\right)\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{u}\left(n\right) = L \cdot \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{e}\left(n\right)\right), \operatorname{mulVec}\left(\operatorname{T}\left(c, n\right), \operatorname{e}\left(n\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.recurrence_eq_toeplitz_ones_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted reconstruction and the signed count give this sequence-to-matrix identity. Conjugation and c(0)=1 give its real part. The existing toeplitzMatrix(c,n-1) is transported through the value-preserving equivalence Fin(n-1+1) to Fin(n); the submatrix and dot-product equivalence theorems also transport the all-ones vector. No measure representation is a premise.

**Theorem 1.4 (Full Toeplitz positivity).**

$$\forall u \in \mathbb{N}\to\mathbb{R},\; \forall L \in \mathbb{R},\; \forall c \in \mathbb{Z}\to\mathbb{C},\; \operatorname{u}\left(0\right) = 0 \Rightarrow \left(\operatorname{u}\left(1\right) = L \Rightarrow \left(0 \le L \Rightarrow \left(\operatorname{c}\left(0\right) = 1 \Rightarrow \left(\left(\forall k \in \mathbb{Z},\; \operatorname{c}\left(0 - k\right) = \operatorname{star}\left(\operatorname{c}\left(k\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{u}\left(n + 1\right) - 2 \cdot \operatorname{u}\left(n\right) + \operatorname{u}\left(\operatorname{NatSub}\left(n, 1\right)\right) = 2 \cdot L \cdot \operatorname{re}\left(\operatorname{c}\left(\operatorname{Int}\left(n\right)\right)\right)\right) \Rightarrow \left(\left(\forall N \in \mathbb{N},\; \operatorname{PosSemidef}\left(\operatorname{toeplitzMatrix}\left(c, N\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 0 \le \operatorname{u}\left(n\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.recurrence_nonneg_of_toeplitz_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding quadratic identity and Mathlib's PosSemidef.re_dotProduct_nonneg give the nonnegative coefficient for every positive size. The prescribed initial value supplies size zero.

**Theorem 1.5 (A negative spectral obstruction).**

$$\forall u \in \mathbb{N}\to\mathbb{R},\; \forall L \in \mathbb{R},\; \forall c \in \mathbb{Z}\to\mathbb{C},\; \operatorname{u}\left(0\right) = 0 \Rightarrow \left(\operatorname{u}\left(1\right) = L \Rightarrow \left(0 \le L \Rightarrow \left(\operatorname{c}\left(0\right) = 1 \Rightarrow \left(\left(\forall k \in \mathbb{Z},\; \operatorname{c}\left(0 - k\right) = \operatorname{star}\left(\operatorname{c}\left(k\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{u}\left(n + 1\right) - 2 \cdot \operatorname{u}\left(n\right) + \operatorname{u}\left(\operatorname{NatSub}\left(n, 1\right)\right) = 2 \cdot L \cdot \operatorname{re}\left(\operatorname{c}\left(\operatorname{Int}\left(n\right)\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(0 < L \Rightarrow \left(\operatorname{u}\left(n\right) < 0 \Rightarrow \left(\exists hT \in \operatorname{IsHermitian}\left(\operatorname{T}\left(c, n\right)\right),\; \operatorname{eigenvaluesZero}\left(\mathit{hT}, \operatorname{last}\left(n\right)\right) \le \frac{\operatorname{u}\left(n\right)}{\operatorname{Real}\left(n\right) \cdot L} \land \frac{\operatorname{u}\left(n\right)}{\operatorname{Real}\left(n\right) \cdot L} < 0\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.negative_recurrence_bounds_smallest_eigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classical finite-dimensional Rayleigh infimum theorem is supplied by Mathlib's hasEigenvalue_iInf_of_finiteDimensional. The public eigenvalue enumeration and its antitonicity put the last eigenvalue below that infimum. Evaluation uses WithLp.toLp(2,e(n)), whose squared Euclidean norm is n and which is nonzero. Conjugate symmetry identifies the real numerator with the preceding quadratic identity. Strict positivity of n times L gives the second inequality.

**Theorem 1.6 (Two-point absolute bound).**

$$\forall u \in \mathbb{N}\to\mathbb{R},\; \forall L \in \mathbb{R},\; \forall c \in \mathbb{Z}\to\mathbb{C},\; \operatorname{u}\left(0\right) = 0 \Rightarrow \left(\operatorname{u}\left(1\right) = L \Rightarrow \left(0 \le L \Rightarrow \left(\operatorname{c}\left(0\right) = 1 \Rightarrow \left(\left(\forall k \in \mathbb{Z},\; \operatorname{c}\left(0 - k\right) = \operatorname{star}\left(\operatorname{c}\left(k\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \operatorname{u}\left(n + 1\right) - 2 \cdot \operatorname{u}\left(n\right) + \operatorname{u}\left(\operatorname{NatSub}\left(n, 1\right)\right) = 2 \cdot L \cdot \operatorname{re}\left(\operatorname{c}\left(\operatorname{Int}\left(n\right)\right)\right)\right) \Rightarrow \left(\left(\forall N \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(2\right)\to\operatorname{Fin}\left(N + 1\right),\; \operatorname{Injective}\left(p\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{submatrix}\left(\operatorname{toeplitzMatrix}\left(c, N\right), p, p\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \left|\operatorname{u}\left(n\right)\right| \le L \cdot \left(\operatorname{Real}\left(n\right) + 2 \cdot \sum_{k\in \operatorname{Ico}\left(1, n\right)} {\operatorname{Real}\left(n\right) - \operatorname{Real}\left(k\right)}\right) \land L \cdot \left(\operatorname{Real}\left(n\right) + 2 \cdot \sum_{k\in \operatorname{Ico}\left(1, n\right)} {\operatorname{Real}\left(n\right) - \operatorname{Real}\left(k\right)}\right) = L \cdot \operatorname{Real}\left(n\right)^{2}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.two_point_posSemidef_abs_recurrence_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only injective two-point principal compressions are assumed positive. Selecting indices zero and k in the block of size k+1 gives determinant one minus the squared complex norm of c(k). Mathlib's determinant nonnegativity and two-by-two determinant formula bound that norm by one. The repository's quadratic_of_bounded_second_difference then supplies the absolute growth bound. Mathlib's finite Gauss identity evaluates the displayed sum, also at zero and one. Full-matrix positivity is not needed for this bound.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.negative_recurrence_bounds_smallest_eigenvalue`
- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.recurrence_eq_toeplitz_ones_quadratic`
- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.recurrence_eq_weighted_curvature_sum`
- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.recurrence_nonneg_of_toeplitz_posSemidef`
- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.toeplitz_ones_diagonal_count`
- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.two_point_posSemidef_abs_recurrence_bound`
- Dependency: [D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree](../Probability/CanonicalLiCurvatureZeroFree.md)
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](LiCurvatureCriterion.md)
