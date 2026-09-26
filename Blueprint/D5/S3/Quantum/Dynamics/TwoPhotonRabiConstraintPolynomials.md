# The constraint polynomials of the two-photon Rabi model at and beyond the critical coupling

## Abstract

The constraint polynomials of the two-photon asymmetric quantum Rabi model factor into linear terms y + 2n(2n + 2rho - 1) at the critical coupling x = 1, and for x > 1 and nonnegative bias all their coefficients are positive, because the tridiagonal matrix behind them is positive definite.

**Definition 1.1 (The constraint polynomials).**

$$((\operatorname{constraintPoly}\left(N, rho, eps, x, 0\right) = 1) \land (\operatorname{constraintPoly}\left(N, rho, eps, x, 1\right) = X + 2 \cdot x \cdot (4 \cdot N + 2 \cdot rho + 2 \cdot eps - 1) - 4 \cdot (1 + eps))) \land (\forall k \in \mathbb{N},\; \operatorname{constraintPoly}\left(N, rho, eps, x, k + 2\right) = (X + 2 \cdot x \cdot (k + 2) \cdot (4 \cdot N + 2 \cdot rho - 2 \cdot (k + 2) + 2 \cdot eps + 1) - 4 \cdot (k + 2) \cdot (k + 2 + eps)) \cdot \operatorname{constraintPoly}\left(N, rho, eps, x, k + 1\right) - 4 \cdot (k + 2) \cdot (k + 1) \cdot (2 \cdot (N - (k + 2) + 1) + rho) \cdot (2 \cdot (N - (k + 2) + 1) + rho - 1) \cdot x \cdot \operatorname{constraintPoly}\left(N, rho, eps, x, k\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.constraintPoly` (`✓ std3`).

*Citation.* Cid Reyes-Bustos, Masato Wakayama (2026). *Two-photon quantum Rabi models – Spectral degeneracy and symmetries*. DOI: [10.48550/arXiv.2609.00750](https://doi.org/10.48550/arXiv.2609.00750). URL: <https://arxiv.org/abs/2609.00750v1>.

*Commentary.*

Definition 4.1 of the source, read as polynomials in y with real parameters x, bias eps and parity rho, and the index N of the constraint polynomial P_N.

**Definition 1.2 (The conjecture).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; \forall rho \in \mathbb{R},\; ((rho = 0) \lor (rho = 1)) \Rightarrow ((\forall eps \in \mathbb{R},\; \operatorname{constraintPoly}\left(N, rho, eps, 1, N\right) = \prod_{n \in \operatorname{Finset.Icc}\left(1, N\right)} (X + 2 \cdot n \cdot (2 \cdot n + 2 \cdot rho - 1))) \land (\forall eps \in \mathbb{R},\; (0 \le eps) \Rightarrow (\forall x \in \mathbb{R},\; (1 < x) \Rightarrow (\forall i \in \mathbb{N},\; (i \le N) \Rightarrow (0 < \operatorname{coeff}\left(\operatorname{constraintPoly}\left(N, rho, eps, x, N\right), i\right)))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.claim` (`✓ std3`).

*Citation.* Cid Reyes-Bustos, Masato Wakayama (2026). *Two-photon quantum Rabi models – Spectral degeneracy and symmetries*. DOI: [10.48550/arXiv.2609.00750](https://doi.org/10.48550/arXiv.2609.00750). URL: <https://arxiv.org/abs/2609.00750v1>.

*Commentary.*

The first statement is taken for every real bias. The second statement is taken for bias eps >= 0, the sign the source uses when it derives the constraint condition; for eps = -2, N = 1 and rho = 0 one has P_1 = y - 2x + 4, which is negative at y = 0 once x > 2.

**Theorem 1.3 (Proof of the conjecture for nonnegative bias).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.result` (`✓ std3`). ∎

*Resolves.* `Problems/reyes-bustos-wakayama-2026-two-photon-rabi-constraint-polynomials` (proved) by `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"reyes-bustos-wakayama-2026-two-photon-rabi-constraint-polynomials","declaration_gid":"D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Cid Reyes-Bustos, Masato Wakayama (2026). *Two-photon quantum Rabi models – Spectral degeneracy and symmetries*. DOI: [10.48550/arXiv.2609.00750](https://doi.org/10.48550/arXiv.2609.00750). URL: <https://arxiv.org/abs/2609.00750v1>.

*Commentary.*

Part (a). At x = 1 the bias cancels from the recursion. In the basis of partial products Q_i = (y + lambda_1)...(y + lambda_i), with lambda_n = 2n(2n + 2rho - 1), the polynomial P_k(1, y) has coefficient C(k, i) 4^(k-i) (N-i-1)(N-i-2)...(N-k) (k+1)k...(i+2) at Q_i. Since y Q_i = Q_(i+1) - lambda_(i+1) Q_i, the recursion for these coefficients reduces to a polynomial identity that holds exactly when rho^2 = rho. At k = N every coefficient with i < N contains the factor N - N = 0, so P_N(1, y) = Q_N. Part (b). P_k(x, y) is det(y + J) for the symmetric tridiagonal matrix J(x) with diagonal entries d_k(x) = 2xk(4N + 2rho - 2k + 2eps + 1) - 4k(k + eps) and off-diagonal entries the square roots of the nonnegative couplings b_k x; expanding the determinant along the first row gives the recursion. By part (a) the eigenvalues of J(1) are the numbers lambda_n > 0, so J(1) is positive definite. For x >= 1 and eps >= 0, J(x) = sqrt(x) J(1) + D with D diagonal and D_k = 2k(sqrt(x) - 1)(sqrt(x)(4N + 2rho - 2k + 2eps + 1) + 2(k + eps)) >= 0, so J(x) is positive definite. Its eigenvalues mu_i are positive, P_N(x, y) is the product of the factors y + mu_i, and every coefficient is a sum of products of the mu_i, hence positive.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.constraintPoly`
- Truth anchor: `D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.result`
