# Positive Fredholm Limits Preserve the Negative Real Zero Locus

## Abstract

Locally uniform limits of determinants of finite-rank positive operators have only nonpositive real zeros.

**Theorem 1.1 (Positive matrix determinants factor over the spectrum).**

$$\forall r: \mathbb{N}, \\{}A: Matrix\left(Fin\left(r\right), Fin\left(r\right), \mathbb{C}\right), \\{}w: \mathbb{C}, \\{}PosSemidef\left(A\right) \Rightarrow \\{}det\left(1 + w \cdot A\right) = \prod_{j\in Fin\left(r\right)} {1 + w \cdot eigenvalue\left(A, j\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.positive_matrix_det_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive semidefinite complex matrix is the finite-range model of a finite-rank positive operator. The matrix spectral theorem diagonalizes it by a unitary change of basis. Determinant multiplicativity cancels the unitary factors and leaves the product of one plus the complex argument times each real eigenvalue.

**Theorem 1.2 (Positive spectral determinant limits preserve their zero locus).**

$$\forall r: \mathbb{N} \to \mathbb{N}, \\{}A: {N: \mathbb{N}} \to Matrix\left(Fin\left(r\left(N\right)\right), Fin\left(r\left(N\right)\right), \mathbb{C}\right), \\{}F: \mathbb{C} \to \mathbb{C}, \\{}{{\forall N\in \mathbb{N}, PosSemidef\left(A\left(N\right)\right)} \land {TendstoLocallyUniformly\left((N, w) \mapsto det\left(1 + w \cdot A\left(N\right)\right), F, atTop\right)} \land {F\left(0\right) = 1}} \Rightarrow \\{}\forall w\in \mathbb{C}, F\left(w\right) = 0 \Rightarrow {Im\left(w\right) = 0 \land Re\left(w\right) \le 0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.positive_fredholm_limit_zeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index, the source operator is represented on its finite range by a positive semidefinite Hermitian matrix. Its approximating function is publicly the determinant of the identity plus the complex argument times that matrix. If these determinants converge locally uniformly, and the limit is normalized to one at zero, every zero of the limit has zero imaginary part and nonpositive real part.

The public factorization bridge rewrites each determinant as the finite product over the matrix eigenvalues. Positive semidefiniteness makes those eigenvalues nonnegative. The locally uniform limit argument then compares every off-axis factor with a suitable positive real point; boundedness there prevents a zero away from the nonpositive real axis.

The normalization at zero is displayed as a premise exactly as in the source statement and excludes zero itself as a zero of the limit.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.positive_fredholm_limit_zeros`
- Truth anchor: `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.positive_matrix_det_factorization`
