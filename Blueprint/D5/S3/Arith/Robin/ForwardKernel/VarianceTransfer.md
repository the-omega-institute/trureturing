# Variance transfer

## Abstract

Compact integrability and square-norm estimates for triangular primitives.

**Theorem 1.1 (Interval Cauchy-Schwarz).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_cauchy_schwarz`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_cauchy_schwarz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b>0, if f and f squared are integrable on [0,b], the square of the integral of f is at most b times the integral of f squared.

**Theorem 1.2 (Monotonicity of the variance majorant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.logarithmic_variance_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.logarithmic_variance_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real function t*log(2/t)^2 is increasing on (0,1/16]. Its derivative is log(2/t)^2-2*log(2/t), which is nonnegative on this interval.

**Theorem 1.3 (Compact integrability of increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_comp_integrableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_comp_integrableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If E is locally bounded and measurable, continuous real choices of step and starting point give integrable increments on any compact set, for any Borel measure finite on compact sets. Compact images bound both evaluations of E.

**Theorem 1.4 (Compact integrability of products).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_product_comp_integrableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_product_comp_integrableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two increments of a locally bounded measurable E, each with continuous step and starting point, have integrable product on any compact set with a Borel measure finite on compact sets. This includes rectangular parameter domains used to exchange integrals.

**Theorem 1.5 (Joint square integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_sq_rectangle_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_sq_rectangle_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite rectangle, the square of an increment is integrable with respect to the product of the two restricted Lebesgue measures when the starting point is the first coordinate and the step is any continuous function of both coordinates.

**Theorem 1.6 (Measurability of triangular primitives).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.triangularPrimitive_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.triangularPrimitive_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed real length, the triangular primitive of a locally bounded measurable error function is measurable in its starting point.

**Theorem 1.7 (Integrability of triangular squares).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.triangularPrimitive_sq_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.triangularPrimitive_sq_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square of a fixed-length triangular primitive is integrable on every finite oriented interval. A uniform bound for increments on the parameter rectangle bounds the primitive.

**Theorem 1.8 (The reverse triangle inequality).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_l2_reverse_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_l2_reverse_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For square-integrable real functions f and g on an ordered interval [a,b], the absolute difference between the square roots of their square integrals is at most the square root of the square integral of f-g. This follows from the two triangle inequalities for the L2 norm.

**Theorem 1.9 (The covariance constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.integral_min_unit_square`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.integral_min_unit_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The iterated integral of min(s,t) over the unit square equals 1/3. Splitting the inner integral at t=s gives s-s^2/2.

**Theorem 1.10 (The small-length estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.small_length_triangular_square_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.small_length_triangular_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If E is locally bounded and measurable and satisfies the short-interval mean-square bound, there is C>0 such that, for every sufficiently large X and every 0<U<=X/16, the integral of B_U(x)^2 over [X,2X] is at most C*X*U^3*log(2*X/U)^2. Cauchy-Schwarz, the substitution u=x*theta, enlargement to a fixed rectangle, and Fubini reduce this to the short-interval bound. Monotonicity of theta*log(2/theta)^2 on (0,1/16] bounds its integral.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_comp_integrableOn`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_product_comp_integrableOn`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.increment_sq_rectangle_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.integral_min_unit_square`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_cauchy_schwarz`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.interval_l2_reverse_triangle`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.logarithmic_variance_mono`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.small_length_triangular_square_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.triangularPrimitive_measurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.triangularPrimitive_sq_intervalIntegrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
