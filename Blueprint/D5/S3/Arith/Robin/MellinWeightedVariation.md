# Mellin Weighted Variation

## Abstract

An absolute Mellin moment bounds the full weighted variation of the Robin integral kernel.

For t>1, let w(t)=(log(t)+1)/(t^2*log(t)^2). For positive scale s and positive y, set f(s,y)=s*w(s*y). The clipped kernel q(x,s,y) equals f(s,y) when x/s<y and zero otherwise. At the threshold x/s=y the kernel is zero. Real powers denote Real.rpow.

Write L=log(x), h1=1+1/L and h2=1+2/L+2/L^2. The coefficient C(x,alpha)=x^(alpha-1)/L*(h1+h2/(1-alpha)) is positive for x>1 and 0<alpha<1.

**Theorem 1.1 (Every pointwise prefix has one common bound).**

Lean statement: `D5/S3/Arith/Robin/MellinWeightedVariation.clipped_kernel_prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/MellinWeightedVariation.clipped_kernel_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, every x>1, every y>0 and every 0<alpha<1, the sum over 0<=j<N of (j+1)^alpha*|q(x,j+1,y)-q(x,j+2,y)| is at most C(x,alpha)*y^(-alpha-1). The bound is independent of N.

Put a=x/y. The indicator chi(a,s), equal to one for s<=a and zero otherwise, pays for the single threshold crossing. The decreasing potential max(s,a)^(alpha-1) pays for the smooth kernel decrease. Both differences telescope over adjacent natural scales, retaining the strict cutoff.

**Theorem 1.2 (The pointwise estimate transports to integral prefixes).**

Lean statement: `D5/S3/Arith/Robin/MellinWeightedVariation.generic_weighted_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/MellinWeightedVariation.generic_weighted_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a measurable real function. Assume that |rho(y)|*y^(-alpha-1) is Lebesgue integrable on y>0, and write M(rho,alpha) for its integral. Define P(rho,x,s) as the integral on y>0 of rho(y)*q(x,s,y). For every natural N, x>1 and 0<alpha<1, the sum over 0<=j<N of (j+1)^alpha*|P(rho,x,j+1)-P(rho,x,j+2)| is at most C(x,alpha)*M(rho,alpha).

The Mellin majorant proves absolute integrability of each clipped integral before integral subtraction. The triangle inequality and the finite pointwise sum then give the prefix bound.

**Theorem 1.3 (Summability and the complete infinite sum bound).**

Lean statement: `D5/S3/Arith/Robin/MellinWeightedVariation.mellin_weighted_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/MellinWeightedVariation.mellin_weighted_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable real rho, every x>1 and every 0<alpha<1 with the stated absolute Mellin integrability, the sequence (j+1)^alpha*|P(rho,x,j+1)-P(rho,x,j+2)| is summable over all natural j. Its infinite sum is at most C(x,alpha)*M(rho,alpha). Both conclusions follow from the nonnegative prefix sums with the common bound.

The whole positive y axis is retained, including y<1. Measurability and absolute Mellin integrability are the function hypotheses; continuity and a derivative of rho are not required. Applying this analytic bound to an arithmetic residual still requires its actual Mellin integrability. The estimate supplies no bound on the independent signed arithmetic coefficient sums.

## References

- Truth anchor: `D5/S3/Arith/Robin/MellinWeightedVariation.clipped_kernel_prefix_bound`
- Truth anchor: `D5/S3/Arith/Robin/MellinWeightedVariation.generic_weighted_prefix`
- Truth anchor: `D5/S3/Arith/Robin/MellinWeightedVariation.mellin_weighted_variation`
