# Density-state covariance and its sparse sum

## Abstract

For a finite-dimensional density state, symmetrized covariance satisfies Cauchy-Schwarz. A spectral interval of half width Delta and sparse row supports bound the total absolute covariance.

**Definition 1.1 (Real expectation).**

$$\operatorname{E}\left(\rho, A\right) = \Re \operatorname{tr}\left(\rho A\right)$$

*Formalization.* `D5/S3/Quantum/Information/CovarianceSumBound.expectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state is a positive semidefinite complex matrix of trace one. All carriers are arbitrary finite types; singular states are included.

**Definition 1.2 (Symmetrized covariance).**

$$\operatorname{Cov}\left(\rho, A, B\right) = \frac{\operatorname{E}\left(\rho, AB\right) + \operatorname{E}\left(\rho, BA\right)}{2} - \operatorname{E}\left(\rho, A\right) \operatorname{E}\left(\rho, B\right)$$

*Formalization.* `D5/S3/Quantum/Information/CovarianceSumBound.covariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Hermitian A and B this is one half the expectation of AB+BA minus the product of expectations. A and B need not commute.

**Definition 1.3 (Variance).**

$$\operatorname{Var}\left(\rho, A\right) = \operatorname{E}\left(\rho, {A}^{2}\right) - {\operatorname{E}\left(\rho, A\right)}^{2}$$

*Formalization.* `D5/S3/Quantum/Information/CovarianceSumBound.variance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Variance uses the same state and the same expectation as covariance.

**Theorem 1.4 (Symmetry).**

$$\operatorname{Cov}\left(\rho, A, B\right) = \operatorname{Cov}\left(\rho, B, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.covariance_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the two observables preserves symmetrized covariance.

**Theorem 1.5 (Right additivity).**

$$\operatorname{Cov}\left(\rho, A, B+C\right) = \operatorname{Cov}\left(\rho, A, B\right) + \operatorname{Cov}\left(\rho, A, C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.covariance_add_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed state and A, covariance is additive in its right argument.

**Theorem 1.6 (Self-covariance is variance).**

$$\operatorname{Cov}\left(\rho, A, A\right) = \operatorname{Var}\left(\rho, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.covariance_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two definitions agree on equal observables.

**Theorem 1.7 (Variance is nonnegative).**

$$0 \le \operatorname{Var}\left(\rho, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.variance_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian observable, its centered square has nonnegative expectation.

**Theorem 1.8 (Cauchy-Schwarz in a density state).**

$$\lvert \operatorname{Cov}\left(\rho, A, B\right) \rvert \le \sqrt{\operatorname{Var}\left(\rho, A\right) \operatorname{Var}\left(\rho, B\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.abs_covariance_le` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Weighted matrix inner products and bounded variances in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Matrix/Order.lean>.

*Commentary.*

For Hermitian A and B, centered observables belong to the weighted matrix semi-inner product space. Its real pairing is exactly covariance.

**Theorem 1.9 (Spectral half-width bound).**

$$\operatorname{Var}\left(\rho, A\right) \le {\Delta}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.variance_le_half_width_sq` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Weighted matrix inner products and bounded variances in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Matrix/Order.lean>.

*Commentary.*

Assume Delta is nonnegative and every spectral value of Hermitian A lies in [c-Delta,c+Delta]. Delta is the half width. Continuous functional calculus bounds the square centered at c, and subtracting the squared mean displacement bounds the variance.

**Theorem 1.10 (Sum from variance bounds).**

$$\sum_{x,y \in Q} \lvert \operatorname{Cov}\left(\rho, \operatorname{R}\left(x\right), \operatorname{R}\left(y\right)\right) \rvert \le \operatorname{card}\left(Q\right) b {\Delta}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.covariance_sum_le_of_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite set Q, assume every R(x) is Hermitian, each variance is at most Delta squared, and for each x in Q at most b elements y in Q have nonzero covariance. Summing only these supports gives the bound.

**Theorem 1.11 (Sparse covariance sum bound).**

$$\sum_{x,y \in Q} \lvert \operatorname{Cov}\left(\rho, \operatorname{R}\left(x\right), \operatorname{R}\left(y\right)\right) \rvert \le \operatorname{card}\left(Q\right) b {\Delta}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CovarianceSumBound.covariance_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set Q and a density state, assume all R(x), x in Q, are Hermitian with spectra in [c(x)-Delta,c(x)+Delta], where Delta is nonnegative. For every x in Q the support of y mapped to Cov(R(x),R(y)) has at most b elements in Q. Then the bound follows with N equal to card Q. The support hypothesis is the locality input; the theorem does not derive a propagation or preparation-time bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.abs_covariance_le`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.covariance`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.covariance_add_right`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.covariance_self`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.covariance_sum_le`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.covariance_sum_le_of_variance`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.covariance_symm`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.expectation`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.variance`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.variance_le_half_width_sq`
- Truth anchor: `D5/S3/Quantum/Information/CovarianceSumBound.variance_nonneg`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
