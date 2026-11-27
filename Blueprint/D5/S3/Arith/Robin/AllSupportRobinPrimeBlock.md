# A finite lower bound for the Robin prime cost

## Abstract

A finite weighted Chebyshev integral lower bounds the actual Robin prime cost.

**Theorem 1.1 (Chebyshev theta with the index-two Robin weight).**

Lean statement: `D5/S3/Arith/Robin/AllSupportRobinPrimeBlock.theta_weight_two_block_le_prime_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/AllSupportRobinPrimeBlock.theta_weight_two_block_le_prime_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h at least 8, the prime cost is at least the integral of theta(t) against the index-two Robin weight over (sqrt(2h), h/2]. The reciprocal-square sum on this interval and the theta prefix at sqrt(2h) jointly bound the integral by Abel summation. The lower endpoint enters through the prefix and the upper endpoint enters through the reciprocal-square sum.

## References

- Truth anchor: `D5/S3/Arith/Robin/AllSupportRobinPrimeBlock.theta_weight_two_block_le_prime_cost`
- Dependency: [D5/S3/Arith/Robin/AllSupportRobinCost](AllSupportRobinCost.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel](PriceRecord/Effective/RobinEffectiveAbel.md)
