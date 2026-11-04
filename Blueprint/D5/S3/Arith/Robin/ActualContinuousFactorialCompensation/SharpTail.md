# The exact limit of the literal factorial compensation

## Abstract

The exact limit of the literal factorial compensation.

The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.

**Theorem 1.1 (Cancellation of the nondecaying floor phase).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_centered_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_centered_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, G(x)-ell=(1+gamma+log(x))*harmonicPrimitive(x)-(eta(x)-((1/2-fract(x))*log(x)+L/2))+2*x*T_epsilon(x), where ell=alpha+h1/2, L=log(2*pi), and h1=1+gamma-L.

**Theorem 1.2 (A global real-uniform sharp error).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_sharp_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_sharp_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, abs(G(x)-ell)<=(4*gamma+24)*(1+log(x))/x. The theorem concerns the literal factorial compensation G=Z_h-h1*floor(x)-alpha*(x-1), with alpha=gamma^2+2*ceta-2. No desired estimate or asymptotic is a premise.

**Theorem 1.3 (A positive global constant).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.exists_G_sharp_tail_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.exists_G_sharp_tail_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a real C>0 such that, for every real x>=1, abs(G(x)-(alpha+h1/2))<=C*(1+log(x))/x. The proof supplies C=4*gamma+24.

**Theorem 1.4 (The exact full-real limit).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.tendsto_G_ell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.tendsto_G_ell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As real x tends to positive infinity, the literal G(x) tends to alpha+h1/2. This is the full real limit and retains the noninteger floor intervals. It is consumed by no claimed RH or Fourier positivity conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_centered_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_sharp_tail_bound`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.exists_G_sharp_tail_constant`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.tendsto_G_ell`
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Cancellation](SharpTail/Cancellation.md)
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial](SharpTail/Factorial.md)
