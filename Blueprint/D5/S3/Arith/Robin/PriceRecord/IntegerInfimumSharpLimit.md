# The integer and real prime-prefix infima

## Abstract

Sharp rounding loss for the full prime-prefix Robin infimum.

**Theorem 1.1 (The normalized gap tends to twice the square root of two).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSharpLimit.actual_integer_infimum_sharp_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSharpLimit.actual_integer_infimum_sharp_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P run through the natural numbers and let S be the primes at most P. Write H = theta(S) and ell = log H. Then √H times ell times the difference integerInfimum(S) − (realInfimum(S) − baseline(S)) tends to 2√2 as P tends to infinity. The theorem is unconditional. The integer infimum uses the full image of the baseline-subtracted objective over all supported natural exponents at least one. The real infimum uses the full admissible real image.

Set the price at g(H) and let Q be the value of the real boundary allocation with its tangent correction. For every admissible integer allocation, its normalized objective before scaling is Q plus its total fixed-price loss minus the tangent remainder at its own clock. Summing the exact per-prime integer minima gives Δ. An allocation that realizes all these minima supplies the upper bound Q + Δ. For the lower bound, values below r = 1/√H have relative clock excess at most A = exp(ell times (exp(r) − 1)) − 1. The tangent remainder there is at most A²/ell. Together with values at or above r, this gives the lower bound min(r, Q + Δ − A²/ell) on the whole integer image.

Both prime endpoints P and the natural floor of H eventually include all primes with nonzero loss, so the exact prime-sum limit applies to Δ. Eventually Q + Δ ≤ r, and the integer error Q + Δ − integerInfimum(S) lies between zero and A²/ell. The two exponential divided differences give A/(ell times r) → 1 and hence √H times A² → 0. The real calibration error Q − (realInfimum(S) − baseline(S)) vanishes at the same scale by the real second-order estimate. Adding the scaled real calibration error and subtracting the scaled integer error transfers the limit of the prime sum to the infimum gap.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSharpLimit.actual_integer_infimum_sharp_limit`
- Dependency: [D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature](../Analytic/LogLogGlobalCurvature.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRoundingFullLimit](ActualRoundingFullLimit.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedSupportIntegerActivationEnvelope](FixedSupportIntegerActivationEnvelope.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder](RealInfimumSecondOrder.md)
