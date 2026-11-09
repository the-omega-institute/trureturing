# Integer-length continuous mixed moments

## Abstract

Continuous sampling and bounded variation quadrature transfer the discrete cubic and fourth moments.

**Theorem 1.1 (Integer-length cubic moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.integer_third`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.integer_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<alpha<beta<1/4, a normalized singular series satisfying HL4(beta) and the interval correlation estimates has vanishing continuous cubic mixed moments, uniformly for integer H in [N^alpha,N^beta], interval endpoints in [0,M], and supported bounded variation weights. The absolute error is at most B*delta eventually whenever the supremum-plus-variation bound is B.

**Theorem 1.2 (Integer-length fourth moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.integer_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.integer_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same singular series, Hardy–Littlewood and interval correlation hypotheses, the continuous fourth mixed moment at integer H approaches the integral of the weight times kappa(N,H)^2 times the sum of the three overlap pairings. The error is uniformly at most B*delta on each polynomial length band and bounded endpoint window.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.integer_fourth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousIntegerMoments.integer_third`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly](DiscreteFourthAssembly.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteThirdAssembly](DiscreteThirdAssembly.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds](SamplingErrorBounds.md)
