# Real-shift order of the delayed cooling kernel

## Abstract

The concrete delayed cooling response has an increasing hazard, strictly decreasing positive-shift ratios, and a weak real-shift kernel order.

Fix a positive real delay at most exp(-1). The function E is the finite-sum relaxation with constant equilibrium history. Its positivity makes every ratio below well defined. All times, ages and shifts are real.

**Definition 1.1 (The logarithmic cooling rate).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.hazard`

*Formalization.* `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.hazard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hazard is E evaluated one delay earlier divided by E at the current time. At positive times it is minus the logarithmic derivative of E. On the initial interval it equals the reciprocal of one minus time.

**Theorem 1.2 (Strictly increasing hazard).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.strictMonoOn_hazard`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.strictMonoOn_hazard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before one delay, the hazard derivative is its square. After one delay, its derivative is the hazard times the difference from its value one delay earlier. These two derivative formulas need not agree at one delay. The initial segment is strictly increasing. A first nonpositive late rate would contradict strict increase up to that time, since the delayed value is strictly smaller. Continuity joins the two intervals.

**Theorem 1.3 (Strict order for positive shifts).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.strictAntiOn_relaxation_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.strictAntiOn_relaxation_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive shift w, the ratio E(t+w) divided by E(t) decreases strictly on nonnegative time. Its derivative is the positive ratio times hazard(t) minus hazard(t+w), which is strictly negative.

**Definition 1.4 (The source history kernel).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.responseKernel`

*Formalization.* `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.responseKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel at age s is E(s-tau). In the bath-history integral the age is nonnegative; the same expression also defines its equilibrium extension. On ages from zero through one delay the kernel equals one.

**Theorem 1.5 (Weak comparison for arbitrary real ages).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.kernel_shift_order`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.kernel_shift_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a at most b and a nonnegative time shift t, the shifted value at b times the unshifted value at a is at most the shifted value at a times the unshifted value at b. The assertion holds even for the real equilibrium extension of the ages. On nonnegative base time the ratio order follows from the increasing hazard. On nonpositive base time its denominator is one and its numerator is nonincreasing. Continuity joins the two parts. The comparison is weak because the kernel has an initial plateau. It supplies a kernel inequality for history comparisons, without asserting a history convolution, an attained extremum, or an optimal two-reservoir preparation.

**Theorem 1.6 (Exact mass of every translated tail).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.kernel_tail_mass`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.kernel_tail_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real lower age L with t plus L nonnegative, the kernel at t plus age is integrable over ages greater than L, and its integral is E(t+L). Apply the fundamental theorem of calculus to E(t+age), whose derivative is the negative kernel. Positivity gives the derivative sign and hence its integrability; the exponential bound gives the zero endpoint at infinity. The case t and L both zero normalizes the source history kernel to unit mass.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.hazard`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.kernel_shift_order`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.kernel_tail_mass`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.responseKernel`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.strictAntiOn_relaxation_ratio`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.strictMonoOn_hazard`
- Dependency: [D5/S3/StatisticalMechanics/DelayedCooling/Kernel](Kernel.md)
