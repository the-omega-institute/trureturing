# Logarithmic precision for the tangent correction

## Abstract

The fixed-price and nonlinear integer minimizer gap at every fixed logarithmic order.

**Theorem 1.1 (Centered gap at every fixed logarithmic order).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentLogGap.fixed_price_tangent_correction_log_power_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentLogGap.fixed_price_tangent_correction_log_power_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the primes p ≤ P, with H their sum of log p and L = log H. Let V be the fixed-price minimum at the prefix price 1/(H L), I the nonlinear integer infimum on the same support, and U the second-layer cutoff at the prefix price. For each fixed natural n, as P tends to infinity, Lⁿ times the difference between H L (V − I) and (1 + 1/L) U²/(2H) tends to zero.

The two prefix minimizers bound H L (V − I) by their scaled tangent remainders. For each nonnegative increment u and log H ≥ 1 with H > 1, the quadratic Q = (1 + 1/L) u²/(2H) exceeds that remainder by at most 4(u/H) Q. The moving-price clock estimate compares both increments to U after division by √H at every fixed log order. This controls the difference of the quadratics, and both centered bounds tend to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentLogGap.fixed_price_tangent_correction_log_power_tendsto`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection](FixedPriceTangentCorrection.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativeMovingPriceMinimizerClock](QuantitativeMovingPriceMinimizerClock.md)
