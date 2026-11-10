# Normalization and price corrections

## Abstract

The dyadic normalization separates the position factor from a price correction tending uniformly to one.

Let E be measurable and bounded on compact intervals, let g be a real integrable profile on the unit interval, and write r=(1-theta)/2, U=x/X, B(s,x)=D_(s*x^theta)(x)/sqrt(x^theta*log(x)).

**Theorem 1.1 (Uniform logarithmic bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.logarithmic_factor_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.logarithmic_factor_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>=4 and X<=x<=2X, sqrt(log(x)/log(X)) is at least one and exceeds one by at most log(2)/log(X).

**Theorem 1.2 (The normalized weighted integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.dyadicZ_eq_weighted_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.dyadicZ_eq_weighted_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For theta>0, X>=4, and X<=x<=2X, the normalized response Z equals U^r*sqrt(log(x)/log(X)) times the integral of g(s)*B(s,x)*rho_x(s*x^theta) over the unit interval. The unit-interval substitution is supplied by WeightRemoval.normalized_eq; the remaining factors follow from the positive square roots of the local and dyadic variance scales.

**Theorem 1.3 (Uniform convergence of the price correction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.eventually_normalized_price_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.eventually_normalized_price_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1 there is an eventually nonnegative function eta(X) tending to zero such that |sqrt(log(x)/log(X))*rho_x(s*x^theta)-1|<=eta(X) throughout X<=x<=2X and 0<=s<=1. One may take eta(X)=log(2)/log(X)+4*X^(theta-1). The logarithmic factor is at least one and differs from one by at most log(2)/log(X), while WeightControl.price_bounds and priceRatio_sub_one control the price ratio.

**Theorem 1.4 (Boundedness on a fixed rectangle).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.dyadicB_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.dyadicB_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real theta and each X>=4, there is a finite nonnegative bound for |B(s,x)| on 0<=s<=1 and X<=x<=2X. Compact boundedness of the increments and continuity of the reciprocal positive denominator give this bound. It supplies integrability on fixed rectangles, independently of the uniform moment estimate used in the limit.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.dyadicB_uniform_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.dyadicZ_eq_weighted_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.eventually_normalized_price_factor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.logarithmic_factor_bounds`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs](MomentTransferDefs.md)
