# HoKalmanPredictionBudget

## Abstract

Finite noisy Ho-Kalman reconstruction with explicit arithmetic certificates.

**Definition 1.1 (stateBudget).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.stateBudget`

*Formalization.* `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.stateBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arithmetic recurrence propagates initial input-map error and transition error. It is executable over rational numbers.

**Definition 1.2 (markovBudget).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markovBudget`

*Formalization.* `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markovBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state-error recurrence and the computed output-map budget yield a finite-horizon Markov-parameter error certificate.

**Definition 1.3 (outputErrorBudget).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.outputErrorBudget`

*Formalization.* `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.outputErrorBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every numeric input to this rational budget comes from finite observed samples, the supplied uncertainty, and the actual returned model.

**Theorem 1.4 (cast stateBudget).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_stateBudget`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_stateBudget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction proves that rational budget evaluation agrees with its real semantic interpretation.

**Theorem 1.5 (cast markovBudget).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_markovBudget`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_markovBudget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The computed rational output budget agrees with the corresponding real arithmetic expression.

**Theorem 1.6 (realMatrix pow).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.realMatrix_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.realMatrix_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real interpretation preserves every matrix power, closing the bridge from rational predicted outputs to real behavior.

**Theorem 1.7 (markov error le).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markov_error_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markov_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction through the actual two state systems proves the error recurrence and output inequality. Stability and diagonalizability are unnecessary for these finite-horizon bounds.

**Theorem 1.8 (run prediction error bound).**

Lean statement: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.run_prediction_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.run_prediction_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal theorem bounds every Markov prediction of the actual rational program against every compatible real order-r system by a fully rational certificate. The bound may grow with the horizon; no uniform stability guarantee is asserted.

## References

- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_markovBudget`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.cast_stateBudget`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markovBudget`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.markov_error_le`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.outputErrorBudget`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.realMatrix_pow`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.run_prediction_error_bound`
- Truth anchor: `D5/S3/Observer/Hankel/HoKalmanPredictionBudget.stateBudget`
- Dependency: [D5/S3/Observer/Hankel/NoisyHoKalmanRecovery](NoisyHoKalmanRecovery.md)
