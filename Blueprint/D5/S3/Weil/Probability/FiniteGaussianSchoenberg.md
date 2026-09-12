# FiniteGaussianSchoenberg

## Abstract

Classical finite Gram Schoenberg positivity with the actual entrywise exponential.

**Theorem 1.1 (Entrywise exponential is positive).**

Lean statement: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.entrywise_exp_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.entrywise_exp_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Schur powers with nonnegative factorial weights converge entrywise to the scalar exponential. Every finite real quadratic inequality passes to the limit.

**Theorem 1.2 (Exact zero-sum distance identity).**

Lean statement: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_distance_zero_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_distance_zero_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every zero-sum real vector the squared Gram-distance form is minus twice its original Gram quadratic form.

**Theorem 1.3 (Squared Gram distance has negative type).**

Lean statement: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_distance_conditionally_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_distance_conditionally_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact zero-sum identity and Gram positivity give conditional negative definiteness; singular matrices and repeated points are retained.

**Theorem 1.4 (Real Gaussian positivity).**

Lean statement: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.real_gram_gaussian_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.real_gram_gaussian_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential of negative squared Gram distance factors as positive diagonal congruence of the entrywise exponential of twice the time-scaled Gram matrix.

**Theorem 1.5 (Retain complex coefficient tests).**

Lean statement: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.ofReal_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.ofReal_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real Gram factorization is mapped to complex scalars, proving positivity against every complex vector.

**Theorem 1.6 (Complex Gaussian positivity).**

Lean statement: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_gaussian_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_gaussian_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward finite Gram form of Schoenberg is proved for all nonnegative real times, including zero time. No exponential positivity premise is supplied.

## References

- Truth anchor: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.entrywise_exp_posSemidef`
- Truth anchor: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_distance_conditionally_negative`
- Truth anchor: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_distance_zero_sum`
- Truth anchor: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_gaussian_posSemidef`
- Truth anchor: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.ofReal_posSemidef`
- Truth anchor: `D5/S3/Weil/Probability/FiniteGaussianSchoenberg.real_gram_gaussian_posSemidef`
