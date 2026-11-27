# Abel summation for the effective Robin bound

## Abstract

Abel summation and weighted Chebyshev tails for the effective Robin bound.

The prime reciprocal-square sum uses the real cutoffs a and z, with primes strictly above a and at most z. This matches the actual arithmetic surplus at a = √(2z).

**Theorem 1.1 (Exact finite Abel summation).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.finite_theta_abel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.finite_theta_abel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 1 < a ≤ z, the sum of 1/p² over primes in (a,z] is θ(z)/(z² log z) − θ(a)/(a² log a) plus the interval integral of θ against the weight of order 2.

**Theorem 1.2 (Weighted integral at a prime-power root).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.integrated_root`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.integrated_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real j > 1, k ≥ 1 and x > 1, the order-j weighted tail of ψ(t^(1/k)) is B(j,1/k,log x) plus J(kj,x^(1/k))/k, where B integrates the real power term and J is the native centered Chebyshev tail.

**Theorem 1.3 (Lower bound for the prime sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.theta_abel_from_tails`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.theta_abel_from_tails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 1 < a ≤ z, the same prime sum is at least T(2,a) − T(2,z) − log(4)/(a log a), where T is the weighted θ tail.

**Theorem 1.4 (Normalized root correction).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.normalized_root_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.normalized_root_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every actual zero occurrence has real part 1/2. For real 1 ≤ k ≤ 5 and u > 0 with u/k ≥ log 2, u exp(3u/2) times the sum of B(2,1/k,u) and J(2k,exp(u)^(1/k))/k is at most 2 exp((1/k − 1/2)u)/(2 − 1/k) + (k/20)(2 + 1/u) exp((1/(2k) − 1/2)u).

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.finite_theta_abel`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.integrated_root`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.normalized_root_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.theta_abel_from_tails`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeSquareSurplus](EffectivePrimeSquareSurplus.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound](../../../../Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound.md)
