# Threshold comparison for the concrete delay kernel

## Abstract

The actual delay kernel gives a pointwise threshold bound for bounded signed controls with explicitly integrable initial and future weighted moments.

Fix a positive delay at most exp(-1), nonnegative future time t and nonnegative waiting time w. The signed threshold control is minus one at ages at most w and plus one at older ages. Its kernel convolution is twice E(t+w) minus E(t), by the exact tail-mass formula. This is an analytic comparison of controls; identifying all source histories with these convolutions and proving the physical comparator and its optimizer remain separate obligations.

**Definition 1.1 (The analytic synchronous contrast).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison.synchronousDifference`

*Formalization.* `D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison.synchronousDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define the contrast at time t to be twice E(t+w) minus E(t). At time zero it equals twice E(w) minus one. This definition asserts no optimality, attainment, cooling, or crossover property.

**Theorem 1.2 (Every future moment obeys the threshold bound).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison.threshold_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison.threshold_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be any real function between minus one and one at every positive age. Assume its kernel-weighted integrands at time zero and time t are integrable, and that its initial weighted moment is at least twice E(w) minus one. Then its time-t moment is at least twice E(t+w) minus E(t). To prove this, set lambda to k(t+w) divided by k(w). The real-shift order says that k(t+a) minus lambda k(a) is nonnegative below w and nonpositive above w. Multiplying by u minus the threshold control is therefore nonnegative on both regions. Integrate this inequality, use the exact threshold integrals, and use positivity of lambda and the initial moment bound. The integrability premises are not a claim that every raw source history has already been represented.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison.synchronousDifference`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison.threshold_comparison`
- Dependency: [D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder](ShiftOrder.md)
