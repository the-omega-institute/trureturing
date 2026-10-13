# Native shared-root variance and calibration

## Abstract

Poisson windows, rectangle masses, and shared calibration produce lower bounds for the complete native reference variance. Classical Poisson and hypergeometric estimates are documented in Library/Estimation; the combined variance and calibration contracts are repository-derived.

**Theorem 1.1 (Root box from a center residual).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.root_box_of_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.root_box_of_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F : Real -> Real and real q,x0,x,d,a,b, assume d>0, a>0, StrictMono F, ContinuousOn F on [x0-d,x0+d], DifferentiableOn Real F in that interval's interior, and a<=deriv F u at every interior u. If F x=q, |F x0-q|<=b and b<=a*d, then |x-x0|<=d and a*|x-x0|<=b.

**Theorem 1.2 (Central shared-root bootstrap).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.shared_root_central_bootstrap`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.shared_root_central_bootstrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type iota, outside : iota -> Real and real r,epsilon,N,R,U,q,t,t0,x0,x,w, assume N>0, every cellCounts N R U t j is nonnegative, |t-t0|<=w, calibratedMean outside r epsilon N R U t0 x0=q and calibratedMean outside r epsilon N R U t x=q. Let V0=calibratedVariance outside r epsilon N R U t0 x0. Assume w<V0 and 2*w<=(V0-w)*log(2)/2. Then |x-x0|<=log(2), |x-x0|<=4*w/(V0-w), and (V0-w)/2<=calibratedVariance outside r epsilon N R U t x<=2*(V0+w).

**Theorem 1.3 (Compensated feedback bounds).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real r,epsilon,x,B,D,d,a,b,X, assume 0<a<=D<=b, B>=0, d>=0, checkerboard r epsilon x<=-d, |x|<=X and |x|<=log(2). Then Real.sigmoid x-1/2-B*Real.sigmoid x*(1-Real.sigmoid x)*checkerboard r epsilon x/D lies between B*d/(8*b)-X/4 and X/4+B/(2*a).

**Theorem 1.4 (Uniform compensated feedback box).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_box`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r with 0<r<1, there exist real d,delta with d>0, delta>0 and delta<=log(2) such that, for all real epsilon,x satisfying |epsilon|<delta and |x|<delta, checkerboard r epsilon x<=-d. The same d and delta work for every epsilon and x in this box.

**Theorem 1.5 (Reference variance on a count window).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_count_window`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_count_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite count window below the calibration threshold contributes a lower bound to the complete reference variance.

**Theorem 1.6 (Signal rectangle mass lower bound).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.signal_rectangle_mass_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.signal_rectangle_mass_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite signal rectangle inside the square-root windows has an explicit lower bound for its native reference mass.

**Theorem 1.7 (Reference variance on a signal window).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_window_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_window_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite signal square-root window supplies a complete reference-variance lower bound while retaining the remaining signal and background counts.

**Theorem 1.8 (Linear reference variance lower bound).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_linear_variance_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_linear_variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete lower-left and upper-right count box yields a linear lower bound for the complete reference variance.

**Theorem 1.9 (Floored signal reference mass).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.floored_signal_reference_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.floored_signal_reference_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native signal reference mass has a uniform floor under the stated compensated-parameter and scale conditions.

**Theorem 1.10 (Native calibration root budget).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_root_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_root_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a compensation parameter in the unit interval, the native calibration root admits the displayed positive budget.

**Theorem 1.11 (Native calibration window budget).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_window_root_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_window_root_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The calibrated root remains within the stated window with the displayed budget under the same parameter range.

**Theorem 1.12 (Anchored central shared calibration).**

Lean statement: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.anchored_central_shared_calibration`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.anchored_central_shared_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full native root anchor drives one shared central calibration curve and its positive compensated response.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.anchored_central_shared_calibration`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_bounds`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.compensated_feedback_box`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.floored_signal_reference_mass`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_root_budget`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.native_calibration_window_root_budget`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_linear_variance_lower`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_count_window`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.reference_variance_window_lower`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.root_box_of_residual`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.shared_root_central_bootstrap`
- Truth anchor: `D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback.signal_rectangle_mass_lower`
- Dependency: [D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge](NativeCalibratedArithmeticBridge.md)
- Dependency: [D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber](NativeSignalConditionalFiber.md)
- Dependency: [D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets](NativeWeightedRowBudgets.md)
