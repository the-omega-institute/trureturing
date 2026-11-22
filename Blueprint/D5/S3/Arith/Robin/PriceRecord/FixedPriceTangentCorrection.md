# Tangent curvature correction on prime prefixes

## Abstract

The tangent curvature correction for the literal integer prime prefix.

**Theorem 1.1 (Unit limit for the scaled gap).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection.fixed_price_tangent_correction_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection.fixed_price_tangent_correction_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural P, use exactly the primes p ≤ P, with each integer exponent at least one. Let H be the sum of log p over this prefix, V the minimum of the fixed-price linear cost at 1/(H log H), and I the infimum of the nonlinear integer cost on the same support. As P tends to infinity, H log H · (V − I) tends to one.

The nonlinear sublevel through the all-ones vector bounds each supported exponent, so a finite product contains an exact minimizer. Concavity makes that vector minimize the linear cost at its own clock price. Eventually the relative price deficit lies between zero and 4(log H)I. The fixed-price minimizer clock theorem applies at both prices and gives a clock increment asymptotic to √(2H) for each vector.

The tangent remainder at the prefix-price minimizer bounds V − I from below. The tangent remainder at the nonlinear minimizer bounds it from above. The quadratic bounds for the log-log tangent gap give limit one for both remainders after multiplication by H log H.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection.fixed_price_tangent_correction_tendsto`
- Dependency: [D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature](../Analytic/LogLogGlobalCurvature.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerAggregate](FixedLayerAggregate.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock](FixedPriceMinimizerClock.md)
