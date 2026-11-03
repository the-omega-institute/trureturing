# Floor-uniform arithmetic identities

## Abstract

Floor-uniform arithmetic identities.

The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.

**Theorem 1.1 (Exact logarithmic harmonic tail).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.J_tail_from_slope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.J_tail_from_slope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, 2*J(x)=log(x)^2-gamma^2+alpha+2*log(x)*epsilon(x)+2*T_epsilon(x). This is algebraically derived from Basic.compensation and is consumed by the literal G decomposition.

**Theorem 1.2 (Exact tail decomposition of the literal G).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.G_tail_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.G_tail_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, G(x)=alpha+(1+gamma)*fract(x)-eta(x)+x*(1+gamma+log(x))*epsilon(x)+2*x*T_epsilon(x). The proof consumes finite_smoothing and the public slope identity; it adds no arithmetic premise.

**Theorem 1.3 (A bounded compensated harmonic primitive).**

Lean statement: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.harmonicPrimitive_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.harmonicPrimitive_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=1, abs(x*epsilon(x)+fract(x)-1/2)<=4/x. The entire real floor phase is retained. The proof consumes the two-sided public harmonic remainder bracket in RobinRationalBasis and elementary logarithm inequalities.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.G_tail_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.J_tail_from_slope`
- Truth anchor: `D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.harmonicPrimitive_bound`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../../GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/Basic](../Basic.md)
