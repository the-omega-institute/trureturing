# Residual-Certified Linear Model Reduction

## Abstract

Constructed reduced state models admit exact residual recurrences, finite-horizon output certificates and explicit uniform error bounds under contraction.

**Definition 1.1 (Driven discrete-time state).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state starts at zero and evolves by x(n+1)=A x(n)+B u(n). The estimates below concern arbitrary bounded or unbounded input sequences as stated in each theorem.

**Definition 1.2 (Construct the reduced dynamics).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedDynamics`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedDynamics` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reduced carrier W has transition P A J. This is a genuine state transition, so the result is not an unconstrained low-rank approximation to a Hankel matrix.

**Definition 1.3 (Construct the reduced input map).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedInput`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reduced input is P B, built from the same projection map used in the reduced dynamics.

**Definition 1.4 (Construct the reduced output map).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedOutput`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reduced output is C J. Predicted outputs are therefore compared in the original output space.

**Definition 1.5 (A reduced model in the existing interface).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.projectedRealization`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.projectedRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When W is finite-dimensional, the constructed maps give the existing FiniteLinearRealization interface. The error estimates do not require P J=id; imposing that identity gives the usual retraction interpretation. A smaller-dimensional W must be chosen separately.

**Definition 1.6 (Compute the transition residual).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.dynamicsResidual`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.dynamicsResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous linear map A J minus J A_r measures failure of the lift to intertwine the full and reduced dynamics. Its operator norm appears explicitly in the error certificate.

**Definition 1.7 (Compute the input residual).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.inputResidual`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.inputResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous linear map B minus J B_r measures the missing input contribution. Its operator norm is the second computable residual in the certificate.

**Definition 1.8 (Compare full and lifted reduced states).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError`

*Formalization.* `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both states are produced by their actual driven recurrences. Their difference is x(n)-J z(n); no error equation is assumed as a premise.

**Theorem 1.9 (Derive the exact error recurrence).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding both state updates and applying linearity gives e(n+1)=A e(n)+(A J-J A_r)z(n)+(B-J B_r)u(n). This proof is the algebraic starting point for all bounds.

**Theorem 1.10 (Finite-time residual certificate).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_le_residual_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_le_residual_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At horizon n the state error is bounded by a finite convolution of powers of the full operator norm with the computed transition and input residual contributions. No stability or contraction assumption is needed.

**Theorem 1.11 (Finite-time output certificate).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_le_residual_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_le_residual_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the original output operator to the state-error bound. The resulting computable finite sum compares outputs of the full model and the constructed reduced model.

**Theorem 1.12 (Uniform state bound for bounded inputs).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState_norm_le_of_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState_norm_le_of_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For input norm bounded by nonnegative M and operator norm of A strictly below one, every zero-initial state has norm at most norm(B) times M divided by one minus norm(A).

**Theorem 1.13 (Explicit uniform reduction error).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_uniform_of_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_uniform_of_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the actual full and reduced dynamics are both contractions, their output difference is uniformly bounded by norm(C) times the sum of the transition-residual contribution and input-residual contribution, divided by one minus norm(A). The reduced-state contribution has its own denominator one minus norm(A_r). These are strict operator-norm hypotheses in the chosen norms, not merely spectral-radius stability.

**Theorem 1.14 (Exact preservation from zero residuals).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedRealizationError.zero_residuals_preserve_outputs`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedRealizationError.zero_residuals_preserve_outputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both computed residual maps vanish, every output agrees at every time for arbitrary input sequences. This exact endpoint follows from the finite residual certificate and does not require contraction.

## References

- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState_norm_le_of_contraction`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.dynamicsResidual`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.inputResidual`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_le_residual_sum`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_uniform_of_contraction`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.projectedRealization`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedDynamics`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedInput`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.reducedOutput`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_le_residual_sum`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_succ`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedRealizationError.zero_residuals_preserve_outputs`
- Dependency: [D5/S3/Observer/Hankel/HankelMinimalStateDimension](HankelMinimalStateDimension.md)
