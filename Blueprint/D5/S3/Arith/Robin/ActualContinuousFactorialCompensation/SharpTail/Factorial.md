# A factorial remainder uniform in floor phase

## Abstract

A factorial remainder uniform in floor phase.

The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.

**Theorem 1.1 (A quantitative logarithmic Stirling remainder).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.log_factorial_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.log_factorial_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural n, the difference between log(n!) and n*log(n)-n+log(n)/2+log(2*pi)/2 is between zero and 1/(12*n). The upper estimate is supplied by the reusable Grid logarithmic factorial envelope, whose proof telescopes Mathlib's Robbins step to its certified Stirling limit; the lower estimate is the public logarithmic Stirling inequality.

**Theorem 1.2 (The literal factorial error at every real cutoff).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.eta_phase_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.eta_phase_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, abs(eta(x)-((1/2-fract(x))*log(x)+log(2*pi)/2))<=4/x. Here eta is the existing literal factorial residual. This estimate includes x=1, all integer cutoffs, and every point inside each floor cell.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.eta_phase_bound`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.log_factorial_remainder`
- Dependency: [D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound](../../../FactorialRatio/GridAntidiagonalTrafficBound.md)
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic](../Basic.md)
