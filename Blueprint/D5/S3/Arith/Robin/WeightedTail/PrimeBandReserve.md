# A bound in terms of the number of primes in the band

## Abstract

A prime-band reserve for the logarithmic Robin slack

**Definition 1.1 (The finite prime band).**

Lean statement: `D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve.primeBand`

*Formalization.* `D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve.primeBand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real y, the band is the finite set of primes at most the natural floor of 2√y, excluding the primes at most the natural floor of √(2y).

**Theorem 1.2 (Each prime contributes at least 1/(16y)).**

$$\forall n \in \mathbb{N},\; 16 \le \operatorname{log}\left(n\right) \Rightarrow \frac{\left|\operatorname{B}\left(\operatorname{log}\left(n\right)\right)\right|}{16 \cdot \operatorname{log}\left(n\right)} \le \operatorname{robinLogMargin}\left(n\right) - \operatorname{J}\left(\operatorname{log}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve.primeBand_reserve_le_robinLogSlack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural number n with y = log(n) ≥ 16, let B(y) consist of the primes p with √(2y) < p ≤ 2√y. Let J(y) be the complete weighted Chebyshev tail.

The complete Mertens ledger cancels the boundary term against the signed difference of the divisor and cutoff Mangoldt costs. The Robin slack equals the sum of the local Euler gaps, the signed weights of missing terms through y, and the negated signed weights of extra terms above y. Each of these sums is nonnegative term by term.

A band prime of valuation zero contributes its missing first power. A prime of valuation one contributes its local Euler gap. A prime of valuation at least two contributes its square above the cutoff. Each contribution is at least 1/(16y), and the primes use distinct terms in these sums.

## References

- Truth anchor: `D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve.primeBand`
- Truth anchor: `D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve.primeBand_reserve_le_robinLogSlack`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../CompleteMertensPeak.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus](../PriceRecord/FullPrimePowerArithmeticSurplus.md)
- Dependency: [D5/S3/Weil/GronwallLowerEnvelope](../../../Weil/GronwallLowerEnvelope.md)
