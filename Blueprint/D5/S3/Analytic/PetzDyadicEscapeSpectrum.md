# Inversion obstruction for the finite diagonal Petz profile

## Abstract

In the finite diagonal Petz strip-Gram model, equal-mean rate laws can have uniformly close scale profiles while remaining separated in Wasserstein distance.

**Definition 1.1 (Finite diagonal rate profile).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.rateProfile`

*Formalization.* `D5/S3/Analytic/PetzDyadicEscapeSpectrum.rateProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite family of real rates rᵢ and real weights wᵢ, sum the strip Gram on the diagonal at −srᵢ with weights wᵢ and divide by the real scale s. For s ≠ 0 each summand is wᵢ (exp(−srᵢ) − 1 + srᵢ)/s. The profile is zero at s = 0. Before division, the sum equals the Laplace transform of the weighted rates minus the total weight plus s times the first rate moment.

**Theorem 1.2 (Uniform error for diagonal logarithmic ratios).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.diagonal_log_ratio_profile_error`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeSpectrum.diagonal_log_ratio_profile_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix ε > 0, nonnegative rates rᵢ and positive weights wᵢ. The diagonal source values are εwᵢ and the reference values are exp(−rᵢ/ε). Assume every logarithmic ratio log(exp(−rᵢ/ε)) − log(εwᵢ) is nonpositive. For every real s > 0, evaluate each diagonal strip Gram at sε times that ratio, sum with weights wᵢ and divide by s. The absolute error relative to the finite rate profile is at most ε times the sum of wᵢ |log(εwᵢ)| over the finite index set.

The diagonal kernel exp(x) − 1 − x is one-Lipschitz on the nonpositive half-line. The frequency shift from −srᵢ is −sε log(εwᵢ), so division by s removes the scale from the bound.

**Theorem 1.3 (Derivative at nonzero scales).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.hasDerivAt_rateProfile`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeSpectrum.hasDerivAt_rateProfile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite real rates and weights and every real s ≠ 0, the derivative is the weighted sum of (1 − (1 + srᵢ) exp(−srᵢ))/s². Apply the quotient rule to each diagonal summand.

**Theorem 1.4 (Exact difference of the even and odd binomial profiles).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.binomial_profile_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeSpectrum.binomial_profile_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural number n > 1 and real r₀ and η, take rates r₀ + jη for j from 0 through n. Each law assigns weight (n choose j)/2^(n−1) on its own parity of j and zero on the other parity. The two laws have unit mass and equal first rate moments, so the affine terms in their profiles cancel.

The binomial theorem gives the even profile minus the odd profile as exp(−sr₀)(1 − exp(−sη))^n / (2^(n−1) s) at every real s ≠ 0. At s = 0 both profiles are zero.

**Theorem 1.5 (Equal-mean coalescing laws with m atoms each).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.coalescing_binomial_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeSpectrum.coalescing_binomial_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural number m ≥ 2, set n = 2m − 1. If a > 0 and η > 0 satisfy a + nη ≤ b, the grid a + jη for j from 0 through n is strictly increasing in [a, b]. The even and odd laws on this grid are nonnegative probabilities with exactly m atoms each and the same mean.

For every real s > 0 the absolute profile difference is at most Kη^n, where K = (n−1)! / (2^(n−1) a^(n−1)). The inequality 1 − exp(−sη) ≤ sη leaves the factor exp(−sa) s^(n−1), which is bounded on the positive half-line because a > 0.

Their finite Wasserstein-1 distance is the infimum of coupling costs for absolute rate distance. Each coupling sends the unit mass from even to odd grid indices across a rate distance of at least η, so W₁ ≥ η.

**Theorem 1.6 (Obstruction above the Hölder exponent 1/(2m − 1)).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.no_uniform_holder_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeSpectrum.no_uniform_holder_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural number m ≥ 2, a rate interval [a, b] with 0 < a < b, and α > 1/(2m − 1). There is no C ≥ 0 such that W₁ ≤ Cδ^α for every pair of probability laws on a common strictly increasing grid of 2m rates in [a, b], each with exactly m atoms and with equal means, whenever δ > 0 bounds the absolute difference of their profiles for every real s > 0.

For any proposed C, choose the binomial pair with η small enough that C(Kη^(2m−1))^α < η. The same pair and tolerance δ = Kη^(2m−1) satisfy the discrepancy bound simultaneously at every positive scale, so the obstruction also holds for any choice of positive sample scales.

## References

- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.binomial_profile_difference`
- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.coalescing_binomial_witness`
- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.diagonal_log_ratio_profile_error`
- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.hasDerivAt_rateProfile`
- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.no_uniform_holder_inverse`
- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeSpectrum.rateProfile`
- Dependency: [D5/S3/Analytic/PetzDyadicStripEnergy](PetzDyadicStripEnergy.md)
