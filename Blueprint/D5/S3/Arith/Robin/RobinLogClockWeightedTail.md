# A strict bound for the logarithmic Robin margin

## Abstract

The weighted Mangoldt tail at the logarithm of an integer

**Theorem 1.1 (The full weighted tail and the divisor sum).**

$$\operatorname{J}\left(\operatorname{log}\left(n\right)\right) < \operatorname{robinLogMargin}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/RobinLogClockWeightedTail.weightedTail_lt_robinLogMargin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer n>5040, put y=log(n). The complete weighted Chebyshev tail at y is strictly below the logarithmic Robin margin of n.

At a positive prime valuation, the logarithmic Euler factor is strictly below its finite Mangoldt sum. Sum this bound over the prime factors of n, retaining multiplicity.

Subtract the same cost per unit from each divisor's benefit. The signed terms are nonnegative through y and nonpositive above y. The divisor cost is exactly log(n) and the cutoff cost is ψ(y). Their difference cancels the boundary term in the complete Mertens ledger.

## References

- Truth anchor: `D5/S3/Arith/Robin/RobinLogClockWeightedTail.weightedTail_lt_robinLogMargin`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](CompleteMertensPeak.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus](PriceRecord/FullPrimePowerArithmeticSurplus.md)
- Dependency: [D5/S3/Weil/GronwallLowerEnvelope](../../Weil/GronwallLowerEnvelope.md)
