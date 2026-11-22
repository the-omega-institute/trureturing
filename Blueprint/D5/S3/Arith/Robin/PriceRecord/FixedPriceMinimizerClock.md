# Clock limit for integer Robin minimizers at a moving price

## Abstract

The uniform clock limit of supported fixed-price integer Robin minimizers.

**Theorem 1.1 (Uniform clock bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock.fixed_price_minimizer_clock_eventually_between`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock.fixed_price_minimizer_clock_eventually_between` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H = θ(P) and let the price λ(P) satisfy λ(P) H log H → 1. Minimize the integer linear cost on the primes p ≤ P, with each exponent at least one. For any l < √2 < r, every minimizer at each sufficiently large P has clock increment strictly between l√H and r√H. The lower cutoff on P is common to all the minimizers at the given prices.

Comparing one-coordinate neighbors gives the included and excluded marginal-price inequalities, with ties allowed on either side. The second layer is bounded between the prime log sums at c√H and d√H for any fixed 0 < c < √2 < d. The prime number theorem gives the limits c and d after normalization. For every included layer j ≥ 3, the price inequality bounds p^j by B = 4H log H for large P. These layers contribute at most (log B / log 2) θ(B^(1/3)), which is o(√H).

**Theorem 1.2 (Limit for all minimizing selections).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock.fixed_price_minimizer_clock_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock.fixed_price_minimizer_clock_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any moving price whose ratio to the prefix price tends to one, let a(P) be any eventual selection of supported minimizers of the literal linear cost. The sum of (a(P)(p) − 1) log p over the support, divided by √H, tends to √2. The uniform two-sided bounds apply to the selected exponent vector at every sufficiently large prefix.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock.fixed_price_minimizer_clock_eventually_between`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock.fixed_price_minimizer_clock_tendsto`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation](FixedLayerFiniteActivation.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff](HigherLayerClampedCutoff.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSecondOrder](IntegerInfimumSecondOrder.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary](RealInfimumPrimeBoundary.md)
