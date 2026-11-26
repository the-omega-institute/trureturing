# Gaussian exponential-focusing phase transition

## Abstract

The weighted covariance trace determines almost-sure focusing, strong operator limits, and vacuum sublevel probabilities for an independent Gaussian multiplication clock.

Consider independent centered Gaussian coordinates with variances vₖ and nonnegative weights αₖ. The partial energy Tₙ sums αₖXₖ² over the first n modes. The full energy T and the mean A = ∑ₖ αₖvₖ take values in the extended nonnegative reals.

**Theorem 1.1 (One-mode Laplace transform).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_quadratic_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_quadratic_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At positive tilt t, integrating exp(−tαX²) under a centered Gaussian law of variance v gives 1/√(1 + 2tαv). The formula includes zero weights and zero variances.

**Theorem 1.2 (Laplace transform at finite mode cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.finite_gaussian_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.finite_gaussian_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Independence gives the product of the one-mode transforms for E[exp(−tTₙ)] at every positive t.

**Theorem 1.3 (Limit of the independent Laplace products).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_gaussian_laplace_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_gaussian_laplace_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For each positive tilt the finite products converge by dominated convergence to E[exp(−tT)], with the integrand assigned zero at T = ∞.

**Theorem 1.4 (Logarithmic formula for the Laplace integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_laplace_eq_log_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_laplace_eq_log_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For every t > 0 the full Laplace integral equals exp(−½ ∑ₖ log(1 + 2tαₖvₖ)), with value zero when the nonnegative sum of logarithms is infinite.

**Theorem 1.5 (Mean of the full energy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.lintegral_totalEnergy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.lintegral_totalEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Tonelli and the Gaussian second moments give the extended expectation E[T] = A, using only the one-coordinate laws.

**Theorem 1.6 (Vanishing transform in the divergent phase).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_laplace_eq_zero_of_mass_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_laplace_eq_zero_of_mass_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The finite Laplace product is at most the inverse square root of 1 + 2t Aₙ, where Aₙ is the sum of αₖvₖ over the first n modes. As the partial mean diverges, the transform tends to zero.

**Theorem 1.7 (Equivalent truncated mean criterion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.mass_eq_top_iff_truncated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.mass_eq_top_iff_truncated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The total mean diverges exactly when the series of mode means capped at one diverges.

**Theorem 1.8 (Almost-sure energy dichotomy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

If A is finite, T is finite almost surely and E[T] = A. For every ℓ > 1, Markov's inequality gives γ(T ≤ log ℓ) ≥ 1 − A/log ℓ.

If A is infinite, the full Laplace integral vanishes and positivity on finite energies forces T = ∞ almost surely. The sum of min(αₖvₖ, 1) diverges exactly when A diverges.

**Theorem 1.9 (Finite vacuum probability threshold).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.vacuum_probability_ge_one_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.vacuum_probability_ge_one_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For finite A and δ > 0, a cutoff ℓ > 1 with ℓ ≥ exp(A/δ) gives vacuum sublevel probability at least 1 − δ.

**Theorem 1.10 (Canonical countable Gaussian space).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.exists_canonical_gaussian_focusing_space`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.exists_canonical_gaussian_focusing_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For any variance sequence the coordinate evaluations on the countable Gaussian product measure give a measurable independent family with those Gaussian marginals.

On complex L², the finite resolvent multiplies by L/(L + exp(Tₙ)) for L > 0. The full resolvent uses T and assigns zero at infinite energy. A finite sublevel projection multiplies by the indicator of the event exp(T) ≤ ℓ.

**Theorem 1.11 (Strong removal of the mode cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_finiteResolvent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_finiteResolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For each positive L and every L² vector the finite-mode resolvent tends in norm to the full resolvent. Equation (C.13) removes a focusing-value cutoff. The analogous limit here removes a mode cutoff.

**Theorem 1.12 (Vacuum projection probability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.sublevelProjection_vacuum_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.sublevelProjection_vacuum_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For ℓ ≥ 1 the squared norm of the projected constant-one vacuum equals γ(T ≤ log ℓ).

**Theorem 1.13 (Strong recovery at finite mean).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_operators_of_mass_lt_top`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_operators_of_mass_lt_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At finite A, the full resolvents and the sublevel projections converge strongly to the identity as their parameters grow. For every ℓ > 1 the squared vacuum projection norm is at least 1 − A/log ℓ, giving the limit in Eq. (5.19) within the model.

**Theorem 1.14 (Operator collapse at infinite mean).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_operators_of_mass_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_operators_of_mass_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At infinite A the full resolvent is zero at every positive L and every finite sublevel projection is zero.

**Theorem 1.15 (Strong recovery at fixed mode cutoff).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_finiteResolvent_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_finiteResolvent_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At every fixed mode cutoff, the resolvent tends strongly to the identity as L grows. At infinite A the two orders of limits therefore give different operators.

**Theorem 1.16 (Wick ordering breaks the pointwise lower bound).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.wick_normal_ordered_focusing_below_one_pos_prob`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.wick_normal_ordered_focusing_below_one_pos_prob` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a positive weight α and variance v, the small ball |X| ≤ √(v/2) has positive Gaussian probability and bounds exp(α(X² − v)) above by exp(−αv/2) < 1. The Wick-ordered model thus violates the pointwise hypothesis used in Eqs. (5.21a–d).

**Theorem 1.17 (Dense form domain at finite mean).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.dense_focusingFormDomain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.dense_focusingFormDomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

When A is finite, the vectors with finite weighted integral ∫ exp(T)|f|² dγ are dense in complex L². The sublevel projections approximate every vector by finite-form vectors.

**Theorem 1.18 (Form-domain collapse at infinite mean).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.focusingFormDomain_eq_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.focusingFormDomain_eq_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

When A is infinite, a vector has finite weighted integral only if it vanishes almost everywhere, so the full multiplication form has domain {0}.

These results concern the independent Gaussian multiplication clock. Applying them to Eq. (4.27) requires a comparison to its nonlinear focusing and corner-density factors.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.dense_focusingFormDomain`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.exists_canonical_gaussian_focusing_space`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.finite_gaussian_laplace`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.focusingFormDomain_eq_singleton`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_dichotomy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_operators_of_mass_eq_top`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_focusing_operators_of_mass_lt_top`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_laplace_eq_log_sum`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_laplace_eq_zero_of_mass_eq_top`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.gaussian_quadratic_laplace`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.lintegral_totalEnergy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.mass_eq_top_iff_truncated`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.sublevelProjection_vacuum_norm_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_finiteResolvent`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_finiteResolvent_atTop`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.tendsto_gaussian_laplace_product`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.vacuum_probability_ge_one_sub`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.wick_normal_ordered_focusing_below_one_pos_prob`
