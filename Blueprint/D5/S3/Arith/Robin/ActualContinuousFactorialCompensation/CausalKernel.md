# The Actual Compensated Causal Kernel

## Abstract

The actual causal logarithmic pullback is continuous, absolutely continuous on every real interval, and integrable together with its actual derivative under explicit global L1 budgets.

**Theorem 1.1 (The full causal W1,1 contract).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/CausalKernel.causal_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/CausalKernel.causal_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function r(t) is exp(-t/2)*G(exp(t)) for t>=0 and zero for t<0. The displayed rSlope(t) is exp(-t/2)*(exp(t)*slope(exp(t)) -G(exp(t))/2) for t>=0 and zero otherwise. The arithmetic G, slope, ceta and alpha are the literal functions of the imported owner; all factorial, floor and prime-power contributions remain intact.

The complete theorem states Continuous r, r(0)=0, absolute continuity of r on every real interval with arbitrary real endpoints a,b, and HasDerivAt r (rSlope(t)) t for almost every real t. It also states Integrable r and Integrable (deriv r). Both full real-line integrals of abs(r(t)) and abs(deriv r t) are at most 4*gamma+16. The budgets concern the actual derivative, not merely a named density.

The liftedSlope is exp(t)*slope(exp(t)) for t>=0 and zero otherwise. Its primitive from zero equals G(exp(t)) on the nonnegative branch and zero on the negative branch by monotone exponential substitution and G_eq_integral. The product with exp(-t/2) supplies all-interval absolute continuity and the genuine ae derivative. G(1)=0 joins the origin continuously, so no jump contribution is discarded.

The value majorant is exp(-t/2)*((gamma+2)*t+t^2/2). The derivative majorant is exp(-t/2)*(gamma+2+t+((gamma+2)*t+t^2/2)/2). Gamma integrals evaluate each nonnegative-half-line majorant integral to 4*gamma+16. Measurability and causal vanishing give global integrability; the primitive derivative identifies rSlope with deriv r almost everywhere before the derivative budget is used.

The arithmetic suppliers retain their Terence Tao / Apache-2.0 attribution. Harmonic, divisor, Abel and integral APIs come from Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 with Lean 4.35.0. No RH result or sublinear sufficient moment order is claimed.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/CausalKernel.causal_kernel`
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic](Basic.md)
