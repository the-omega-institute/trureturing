# Variance transfer

## Abstract

Compact integrability and square-norm estimates for profile averages.

**Theorem 1.1 (The unit-interval formula).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.profileAverage_eq_unit_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.profileAverage_eq_unit_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real length h, including h=0, the normalized profile primitive equals the integral of g(s) times the increment of length s*h over the unit interval, divided by h. The substitution u=s*h proves the identity; totalized division handles zero length.

**Theorem 1.2 (Weighted Cauchy-Schwarz).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.profile_cauchy_schwarz`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.profile_cauchy_schwarz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If g is integrable on the unit interval and k is measurable and bounded in absolute value by a nonnegative M, then the square of the integral of g*k is at most the integral of absolute g times the integral of absolute g times k squared. Apply Cauchy-Schwarz to the square root of absolute g and its product with absolute k.

**Theorem 1.3 (Interval Cauchy-Schwarz).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_cauchy_schwarz`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_cauchy_schwarz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b>0, if f and f squared are integrable on [0,b], the square of the integral of f is at most b times the integral of f squared.

**Theorem 1.4 (Monotonicity of the variance majorant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.logarithmic_variance_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.logarithmic_variance_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real function t*log(2/t)^2 is increasing on (0,1/16]. Its derivative is log(2/t)^2-2*log(2/t), which is nonnegative on this interval.

**Theorem 1.5 (Integrability of profile-weighted increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.unit_increment_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.unit_increment_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a locally bounded measurable E and an integrable unit profile g, the function g(s)*(E(x+s*h)-E(x)) is integrable on the unit interval for every real h and x. Compactness bounds the increment, so multiplication by it preserves integrability.

**Theorem 1.6 (Compact integrability of increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_comp_integrableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_comp_integrableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If E is locally bounded and measurable, continuous real choices of step and starting point give integrable increments on any compact set, for any Borel measure finite on compact sets. Compact images bound both evaluations of E.

**Theorem 1.7 (Compact integrability of products).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_product_comp_integrableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_product_comp_integrableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two increments of a locally bounded measurable E, each with continuous step and starting point, have integrable product on any compact set with a Borel measure finite on compact sets. This includes rectangular parameter domains used to exchange integrals.

**Theorem 1.8 (Joint square integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_sq_rectangle_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_sq_rectangle_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite rectangle, the square of an increment is integrable with respect to the product of the two restricted Lebesgue measures when the starting point is the first coordinate and the step is any continuous function of both coordinates.

**Theorem 1.9 (Interval L2 and lpNorm conversion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.lpNorm_two_eq_intervalL2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.lpNorm_two_eq_intervalL2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an almost everywhere measurable real function on an ordered finite interval, its lpNorm at exponent two on the restricted interval measure equals the square-root interval L2 norm.

**Theorem 1.10 (The reverse triangle inequality).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_l2_reverse_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_l2_reverse_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For square-integrable real functions f and g on an ordered interval [a,b], the absolute difference between the square roots of their square integrals is at most the square root of the square integral of f-g. This follows from the two triangle inequalities for the L2 norm.

**Theorem 1.11 (The covariance constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.integral_min_unit_square`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.integral_min_unit_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The iterated integral of min(s,t) over the unit square equals 1/3. Splitting the inner integral at t=s gives s-s^2/2.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_comp_integrableOn`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_product_comp_integrableOn`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_sq_rectangle_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.integral_min_unit_square`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_cauchy_schwarz`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_l2_reverse_triangle`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.logarithmic_variance_mono`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.lpNorm_two_eq_intervalL2`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.profileAverage_eq_unit_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.profile_cauchy_schwarz`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.unit_increment_integrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs](CrossExponentDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
