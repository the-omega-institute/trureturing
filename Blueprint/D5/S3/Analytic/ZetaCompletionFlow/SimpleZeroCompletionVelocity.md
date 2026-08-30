# Simple Zero Completion Velocity

## Abstract

A nondegenerate zero-thread chain equation determines its completion velocity by the ratio of completion and state derivatives.

**Theorem 1.1 (Zero Completion Velocity eq Of Chain).**

$$\forall K: Type, completionDerivative: K, stateDerivative: K, velocity: K, [\operatorname{Field}\left(K\right)],\\{}(stateDerivative \neq 0) \land (completionDerivative + stateDerivative \times velocity = 0) \Rightarrow\\{}(velocity = zeroCompletionVelocity completionDerivative stateDerivative).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_eq_of_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Algebraic extraction of the simple-zero completion velocity from the chain rule identity.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Zero Completion Velocity Satisfies Chain).**

$$\forall K: Type, completionDerivative: K, stateDerivative: K, [\operatorname{Field}\left(K\right)],\\{}(stateDerivative \neq 0) \Rightarrow\\{}(completionDerivative + stateDerivative \times zeroCompletionVelocity completionDerivative stateDerivative = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_satisfies_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution back into the chain equation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Zero Completion Velocity Scale Invariant).**

$$\forall K: Type, c: K, completionDerivative: K, stateDerivative: K, [\operatorname{Field}\left(K\right)],\\{}(c \neq 0) \land (stateDerivative \neq 0) \Rightarrow\\{}(zeroCompletionVelocity (c \times completionDerivative) (c \times stateDerivative) = zeroCompletionVelocity completionDerivative stateDerivative).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_scale_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Common nonzero rescaling of the analytic family leaves zero velocity unchanged.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Zero Completion Velocity eq Zero iff).**

$$\forall K: Type, completionDerivative: K, stateDerivative: K, [\operatorname{Field}\left(K\right)],\\{}(stateDerivative \neq 0) \Rightarrow\\{}(zeroCompletionVelocity completionDerivative stateDerivative = 0 \Leftrightarrow completionDerivative = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a simple zero, vanishing completion velocity is equivalent to vanishing completion-direction forcing.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Zero Completion Velocity ne Zero).**

$$\forall K: Type, completionDerivative: K, stateDerivative: K, [\operatorname{Field}\left(K\right)],\\{}(completionDerivative \neq 0) \land (stateDerivative \neq 0) \Rightarrow\\{}(zeroCompletionVelocity completionDerivative stateDerivative \neq 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero forcing term yields a nonzero velocity at a simple zero.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_eq_of_chain`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_eq_zero_iff`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_ne_zero`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_satisfies_chain`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.zero_completion_velocity_scale_invariant`
