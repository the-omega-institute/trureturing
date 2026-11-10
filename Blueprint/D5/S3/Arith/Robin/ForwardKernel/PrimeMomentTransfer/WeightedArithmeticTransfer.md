# BV weighted arithmetic transfer

## Abstract

BV weighted arithmetic moments agree with their quadratic formal integrals up to a uniform square-root error.

**Theorem 1.1 (Integrability of polynomial logarithmic weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.polynomial_weight_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.polynomial_weight_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least two, a supported bounded variation weight w and any real polynomial p, the function w(x/N) p(log x) is interval integrable over [N,2N].

**Theorem 1.2 (Integrability of weighted formal moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.formal_weight_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.formal_weight_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every singular-series function, length, tuple of endpoints and supported bounded variation weight, the weighted formal moment w(x/N) Phi(log x) is interval integrable over [N,2N] when N is at least two. Each tuple contributes a finite sum of polynomial logarithmic weights.

**Theorem 1.3 (Weighted cubic and fourth arithmetic moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.arithmetic_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.arithmetic_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume zero less than alpha less than beta less than one, the strong four-point Hardy–Littlewood hypothesis, and singular-series values one on the empty set and on singletons. Fix M at least one and positive epsilon. There is a nonnegative C such that, for every sufficiently large real N, every integer H between N to alpha and N to beta, every supported BV weight w with supremum bound plus variation at most B, and every three or four intervals in [0,M], the discrete weighted product of centred von Mangoldt interval sums differs from the integral of w(x/N) times Phi(log x) by at most C B N to the power one half plus epsilon times H to the number of intervals. C and the threshold for N precede all choices of H, weight, number of intervals, and endpoints.

The quadratic reduction expresses every repeated-index tuple using centred distinct products with polynomial logarithmic coefficients. Only a fixed finite family of coefficient polynomials occurs for tuples of length at most four. Apply centred BV correlation estimates uniformly to that family, sum over subsets and shift tuples, and use a smaller Hardy–Littlewood exponent to absorb the logarithms. The repeated-shift collision estimate accounts for proper prime powers and for replacing log(n+d) by log n. This transfer uses no singular-series interval asymptotic hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.arithmetic_transfer`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.formal_weight_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.polynomial_weight_integrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation](CentredCorrelationSummation.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds](CollisionErrorBounds.md)
