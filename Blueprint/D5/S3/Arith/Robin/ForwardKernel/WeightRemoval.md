# Removing the price weight

## Abstract

Von Koch control removes the price weight from the forward kernel.

Write E(x)=psi(x)-x, H(x)=x^(4/5), and T0(x)=sqrt(x)/H(x)^2 times the integral of E(x+u)-E(x) over 0<=u<=H(x). Assume the von Koch bound |E(x)|<=C*sqrt(x)*log(x)^2 for all sufficiently large x.

**Theorem 1.1 (Uniform increment bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.discrepancy_increment_vonKoch_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.discrepancy_increment_vonKoch_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is C>0 such that, for all sufficiently large x and every u in [0,H(x)], |E(x+u)-E(x)| is at most C*sqrt(x)*log(x)^2. Indeed x<=x+u<=2*x, so the von Koch bounds at x and x+u have the same order, uniformly in u.

**Theorem 1.2 (Pointwise weight removal).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.forward_kernel_weight_removal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.forward_kernel_weight_removal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference between the weighted response T(x) and T0(x) is O(log(x)^2). Subtract the two defining integrals and bound the price ratio error by 4*x^(-1/5). The uniform increment bound then gives sqrt(x)/H(x)^2 * H(x) * C*sqrt(x)*log(x)^2 * 4*x^(-1/5) = 4*C*log(x)^2.

**Theorem 1.3 (Negligible squared error on dyadic intervals).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.forward_kernel_weight_removal_l2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.forward_kernel_weight_removal_l2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of (T(x)-T0(x))^2/x over [X,2X], divided by X^(1/5)*log(X), tends to zero. If the pointwise error is at most K*log(x)^2, then log(x)<=2*log(X) and x>=X bound this integral by 16*K^2*log(X)^4. After division the bound is 16*K^2*log(X)^3/X^(1/5), which tends to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.discrepancy_increment_vonKoch_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.forward_kernel_weight_removal`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.forward_kernel_weight_removal_l2`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper](DyadicMeanSquareUpper.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth](MellinPolynomialGrowth.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Transport](Transport.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightControl](WeightControl.md)
