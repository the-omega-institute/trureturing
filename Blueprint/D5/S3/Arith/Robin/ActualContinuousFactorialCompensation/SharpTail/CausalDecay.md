# Weighted decay of the actual centered causal kernel

## Abstract

Weighted decay of the actual centered causal kernel.

The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.

**Theorem 1.1 (The actual kernel after subtracting its leading exponential).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t>=0, abs(r(t)-ell*exp(-t/2))<=(4*gamma+24)*(1+t)*exp(-3*t/2). The function r is the existing causal kernel, equal to exp(-t/2)*G(exp(t)) on t>=0 and zero otherwise. This estimate consumes the arithmetic sharp-tail theorem.

**Theorem 1.2 (Weighted L1 for every real exponent below 3/2).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_weighted_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_weighted_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real a<3/2, the function t -> exp(a*t)*(r(t)-ell*exp(-t/2)) is IntegrableOn (Ioi 0). The proof uses the actual centered estimate and integrable exponential moments. This statement does not establish complex analytic continuation, Fourier-symbol positivity, a zero-free region, RH, or the sufficient sublinear moment target.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_decay`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_weighted_integrable`
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/CausalKernel](../CausalKernel.md)
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail](../SharpTail.md)
