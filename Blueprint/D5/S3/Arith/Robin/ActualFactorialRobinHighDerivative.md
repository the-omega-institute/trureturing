# The Actual Factorial Robin High Integral and Its Derivative

## Abstract

The actual factorial Robin remainder has a complete high-domain integral with a genuine derivative at every positive log scale and explicit value and derivative bounds.

The function eta(y) is the existing arithmetic residual at coefficient k(n)=log n and A=D=1. The exact finite log-prefix identity identifies it with log(floor(y)!)-y*log(y)+y. The actual KernelData instance has C=mu=A=D=1 and uses the original factorial error bound; the remainder includes every factorial source.

**Theorem 1.1 (The complete signed high integral and its derivative).**

Lean statement: `D5/S3/Arith/Robin/ActualFactorialRobinHighDerivative.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualFactorialRobinHighDerivative.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s=exp(r), highKernel(r,y)=s*scaleWeight(s,y) equals s^2*weight(s*y), where weight(t)=(1+log(t))/(t^2*log(t)^2) is the original Robin derivative weight. The complete signed integral E(r)=integral over y>1 of eta(y)*highKernel(r,y) therefore retains the original scaled weight. It is independent of x, with no truncation at infinity.

For every r>0 both the actual high integrand and its parameter derivative are integrable on the whole interval (1,infinity). The pointwise derivative is -eta(y)/y^2 times ((r+log(y))^(-2)+2*(r+log(y))^(-3)). The theorem gives HasDerivAt E Eprime(r) r, where Eprime(r) is the integral of this entire signed derivative integrand.

At each r0>0 the common neighborhood r0/2<r<3*r0/2 admits the integrable derivative majorant ((r0/2)^(-2)+2*(r0/2)^(-3)) times (1+log(y))/y^2 on the whole high domain. The proof calls Mathlib's dominated parameter integral derivative theorem with actual measurability, base integrability and pointwise derivatives. No derivative of the factorial remainder or its floor function is used.

The complete envelope integral equals two. The result gives abs(E(r))<=2*(1/r+1/r^2) and abs(Eprime(r))<=2*(1/r^2+2/r^3) at every positive r. The signed E and Eprime remain the actual full integrals in the statement; their envelopes pay bounds without replacing them.

The original LogConvolutionMassExpansion supplies sum_log_eq_log_factorial and floor_factorial_log_error. MellinWeightedVariation supplies scaleWeight_eq and hasDerivAt_scaleWeight. QuotientIntegralBudget supplies measurable_residual, integrableOn_log_tail and integral_log_tail. All seven declarations are consumed at their existing owners. The finite-log suppliers retain Terence Tao's Apache 2.0 attribution and immutable Mathlib commit 0826a5e4ff8877949060d03ce8955545bfb2b47f.

This theorem pays the complete actual high-domain analytic derivative. The original P_x low/high decomposition and change of variables, the dyadic growth weight, the actual harmonic decay rate and the common critical signed compensation require their additional proofs. No Robin final sign or RH conclusion follows here.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualFactorialRobinHighDerivative.result`
- Dependency: [D5/S3/Arith/LogConvolutionMassExpansion](../LogConvolutionMassExpansion.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
- Dependency: [D5/S3/Arith/Robin/QuotientIntegralBudget](QuotientIntegralBudget.md)
