# NoisyHoKalmanRecovery

## Abstract

Finite noisy Ho-Kalman reconstruction with explicit arithmetic certificates.

**Definition 1.1 (inverseBudget).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.inverseBudget`

*Formalization.* `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.inverseBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of absolute entries of the computed rational inverse is a directly executable certificate quantity.

**Definition 1.2 (aErrorBudget).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.aErrorBudget`

*Formalization.* `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.aErrorBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transition error budget uses the observed transition norm bound, the entrywise noise budget, the selected order, and the positive inverse-margin denominator.

**Definition 1.3 (bErrorBudget).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.bErrorBudget`

*Formalization.* `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.bErrorBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input error budget uses the number of input columns for direct input-block uncertainty and the state order for inverse perturbation.

**Definition 1.4 (cErrorBudget).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.cErrorBudget`

*Formalization.* `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.cErrorBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output block needs no inverse solve, so its error budget is state order times entrywise uncertainty.

**Definition 1.5 (realMatrix).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix`

*Formalization.* `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A semantic bridge interprets rational algorithm outputs as real matrices without changing their coordinates.

**Theorem 1.6 (realMatrix mul).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real interpretation preserves finite matrix multiplication, linking the executable arithmetic to the analysis.

**Theorem 1.7 (realMatrix one).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real interpretation preserves the identity matrix, so the computed inverse identity transports to real analysis.

**Definition 1.8 (realSamples).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realSamples`

*Formalization.* `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realSamples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sample indexing is retained while entries are interpreted in the real field.

**Theorem 1.9 (norm realMatrix le absSum).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.norm_realMatrix_le_absSum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.norm_realMatrix_le_absSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite-sum comparison proves that the rational absolute-entry sum bounds the real induced infinity operator norm.

**Theorem 1.10 (sample noise blocks).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.sample_noise_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.sample_noise_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One uniform sample-error hypothesis yields all four block-error bounds with the correct MIMO dimension factors.

**Theorem 1.11 (run noisy recovery).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.run_noisy_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.run_noisy_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From actual program success, finite real model semantics and entrywise noise, derive true-block nonsingularity, exact true behavior in selected reachable coordinates, and three explicit bounds for the returned matrices. Neither the reference realization nor its coordinate transform is supplied to the program.

**Theorem 1.12 (Noise-compatible model-order lower bound).**

Lean statement: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.run_order_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.run_order_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful rational inverse-margin certificate excludes every real system of dimension below r whose finite Markov parameters lie within the supplied entrywise noise budget. It does not require the comparison system to have order r.

## References

- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.aErrorBudget`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.bErrorBudget`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.cErrorBudget`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.inverseBudget`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.norm_realMatrix_le_absSum`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix_mul`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realMatrix_one`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.realSamples`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.run_noisy_recovery`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.run_order_lower_bound`
- Truth anchor: `D5/S3/Observer/Hankel/NoisyHoKalmanRecovery.sample_noise_blocks`
- Dependency: [D5/S3/Observer/Hankel/ExecutableHoKalman](ExecutableHoKalman.md)
- Dependency: [D5/S3/Observer/Hankel/HoKalmanPerturbation](HoKalmanPerturbation.md)
