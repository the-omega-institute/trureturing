# The concrete delayed relaxation

## Abstract

The finite-sum quasi-exponential relaxation has a constant equilibrium past, is continuous, satisfies its delay equation, and is positive with exponential decay throughout the nonoscillatory delay range.

Fix a positive real delay tau. Time and temperature are real. The relaxation E is the normalized response to a single quench from an equilibrated state. The finite-sum construction is the quasi-exponential in Eq. (6) of Santos, The role of preparation protocols in the Mpemba effect under time-delayed Newton cooling, arXiv:2611.12328v1. These statements concern the scalar delay equation; they do not assert optimality of any preparation protocol.

**Definition 1.1 (The cutoff-power construction).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation`

*Formalization.* `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the definition, each summand uses the minimum of n times tau minus t and zero, raised to the power n plus one and divided by its factorial. Only the first floor(t/tau) plus one summands are needed. Terms beyond the active interval vanish, so a single finite sum represents the function in a neighborhood of each time, even when the floor changes.

**Theorem 1.2 (Agreement with the source finite sum).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_eq_source_sum`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_eq_source_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonnegative time, every included index n satisfies n times tau at most t. The cutoff therefore leaves each summand unchanged. The last term at an integer multiple of tau is zero, so the source endpoint convention agrees with either adjoining polynomial.

**Theorem 1.3 (The equilibrated past).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_of_nonpos`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_of_nonpos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every time at most zero all cutoff terms vanish, and E equals one. This fixes the complete past history rather than only an initial value.

**Theorem 1.4 (The first polynomial segment).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_initial_segment`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_initial_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From zero through one delay, including both endpoints, E is one minus time. At one delay the newly included quadratic term is zero.

**Theorem 1.5 (Continuity at every real time).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.continuous_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.continuous_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each cutoff power is continuous. Local stabilization of the finite sum gives continuity on the whole real line, including zero and all step boundaries.

**Theorem 1.6 (The positive-time delay equation).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.hasDerivAt_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.hasDerivAt_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative is minus E evaluated one delay earlier, at every strictly positive real time. The terms added at positive step boundaries have power at least two; their derivatives vanish at those boundaries. Reindexing the remaining derivative sum gives exactly the delayed relaxation. The extension is not assumed differentiable at zero.

**Theorem 1.7 (The initial derivative jump).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.not_differentiableAt_relaxation_zero`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.not_differentiableAt_relaxation_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equilibrium extension has left derivative zero at the initial quench, whereas the first polynomial segment has right derivative minus one. Consequently the two-sided derivative does not exist there.

**Theorem 1.8 (Positivity in the nonoscillatory delay range).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_pos`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive delay at most exp(-1), E is strictly positive at every real time. Multiply E by exp(kappa times t), choosing kappa equal to exp(1). Its rate at zero is positive. If a first nonpositive rate existed, the weighted response would increase strictly up to that time, including its negative-time exponential history. The delayed differential equation and exp(kappa times tau) at most kappa would make the rate strictly positive there as well, a contradiction.

**Theorem 1.9 (Strict cooling after the quench).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.strictAntiOn_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.strictAntiOn_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the delayed value makes the derivative strictly negative at all positive times. Continuity joins this strict decrease to the value at zero.

**Theorem 1.10 (Monotonicity with the equilibrium extension).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.antitone_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.antitone_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant past and the decreasing nonnegative-time response together give a nonincreasing function on the whole real line.

**Theorem 1.11 (A uniform exponential bound).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_le_exp_neg`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_le_exp_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At nonnegative times, E is at most exp(-t). The derivative of exp(t) times E is nonpositive because E evaluated one delay earlier is at least its current value. At zero the product equals one.

**Theorem 1.12 (Decay to equilibrium).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.tendsto_relaxation_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.tendsto_relaxation_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive response is bounded above by exp(-t), so it tends to zero as time tends to positive infinity. These conclusions include the critical endpoint tau equal to exp(-1); no asymptotic expansion is used.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.antitone_relaxation`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.continuous_relaxation`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.hasDerivAt_relaxation`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.not_differentiableAt_relaxation_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_eq_source_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_initial_segment`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_le_exp_neg`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_of_nonpos`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.relaxation_pos`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.strictAntiOn_relaxation`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/Kernel.tendsto_relaxation_atTop`
