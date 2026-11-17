# Toeplitz positivity of power sums and the unit circle

## Abstract

A finite family closed under inversion in the unit circle lies on the circle exactly when its power-sum Toeplitz matrix is positive semidefinite.

Let u be a family of m nonzero complex numbers that is closed, with multiplicities, under inversion in the unit circle z ↦ 1/conj(z): there is a permutation σ of the indices with u(σ j) = 1/conj(u j). The permutation records the multiplicities; closure of the set of values alone is not enough, since for the multiset {2, 1/2, 1/2} the power sums give p(−1) = 9/2 while p(1) = 3. The Toeplitz matrix is the matrix toeplitzMatrix of LiCurvatureCriterion, whose (j, k) entry for 0 ≤ j, k ≤ N is p(j − k).

**Definition 1.1 (Integer power sums).**

Lean statement: `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.powerSum`

*Formalization.* `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.powerSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

powerSum u k is p(k) = Σ_j u_j^k for an integer k.

**Theorem 1.2 (A family on the unit circle gives positive semidefinite Toeplitz matrices).**

Lean statement: `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.powerSum_toeplitz_posSemidef_of_norm_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.powerSum_toeplitz_posSemidef_of_norm_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family u with |u_j| = 1 for every j, the (N + 1) × (N + 1) matrix with entries p(j − k) is positive semidefinite for every N. No closure hypothesis and no bound relating N to the size of the family is needed.

This is the finite-Dirac-measure case of the circle-moment Toeplitz positivity theorem: when |u_j| = 1 the point 1/u_j lies on the circle and (1/u_j)^(−n) = u_j^n, so p is the moment sequence of the measure Σ_j δ(1/u_j), and the proof applies `D5/S3/Weil/TestFunctions/LiCurvatureCriterion.circle_moment_toeplitz_posSemidef` to that measure.

**Theorem 1.3 (Positive semidefiniteness detects the unit circle).**

Lean statement: `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.toeplitz_posSemidef_iff_norm_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.toeplitz_posSemidef_iff_norm_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Charles Hermite (1856). *Extrait d'une lettre de Mr. Ch. Hermite de Paris à Mr. Borchardt de Berlin sur le nombre des racines d'une équation algébrique comprises entre des limites données*. DOI: [10.1515/crll.1856.52.39](https://doi.org/10.1515/crll.1856.52.39). URL: <https://doi.org/10.1515/crll.1856.52.39>.

*Acknowledgement.* M. G. Krein and M. A. Naimark (1981). *The method of symmetric and Hermitian forms in the theory of the separation of the roots of algebraic equations*. DOI: [10.1080/03081088108817420](https://doi.org/10.1080/03081088108817420). URL: <https://doi.org/10.1080/03081088108817420>.

*Acknowledgement.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

Let u be nonzero and closed under z ↦ 1/conj(z) with multiplicities, witnessed by σ, and let d be the number of distinct values of u. For every N with d ≤ N + 1, the (N + 1) × (N + 1) matrix with entries p(j − k) is positive semidefinite if and only if |u_j| = 1 for every j. Since d ≤ m, this holds in particular for N = m − 1 and every larger N.

Proof: the backward direction is the previous theorem. For the forward direction, for a coefficient vector x with polynomial P(w) = Σ_a x_a w^a, the quadratic form equals Σ_j conj(P(conj u_j)) P(conj u(σ j)), because u_j^(a − b) = u_j^a conj(u(σ j))^b. If some z = u_i has |z| ≠ 1, the points conj(z) and 1/z are distinct nodes among the d values conj(u_j). Lagrange interpolation gives a polynomial of degree below d, hence a coefficient vector of length N + 1, with value 1 at conj(z), value −1 at 1/z and value 0 at the other nodes. Each term of the form is then 0 or −1, and the term with index i is −1, so the form has real part at most −1.

Scope: the theorem does not count negative eigenvalues; the inertia statement that the number of negative eigenvalues equals the number of off-circle pairs is not formalized here. The result belongs to the Hermite–Sylvester method of root separation by quadratic and Hermitian forms, surveyed by Krein and Naimark, and to the theory of Toeplitz forms on the unit circle. A verbatim source for this finite-family form was not found; no novelty is claimed, and the repository's contribution is the formal statement and proof.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.powerSum`
- Truth anchor: `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.powerSum_toeplitz_posSemidef_of_norm_eq_one`
- Truth anchor: `D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.toeplitz_posSemidef_iff_norm_eq_one`
- Truth anchor: `D5/S3/Weil/TestFunctions/LiCurvatureCriterion.circle_moment_toeplitz_posSemidef`
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](LiCurvatureCriterion.md)
