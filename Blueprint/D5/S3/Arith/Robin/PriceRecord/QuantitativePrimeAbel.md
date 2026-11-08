# Quantitative counting and finite Euler deficits

## Abstract

Real-endpoint four-term prime-counting expansion.

A quantitative theta remainder and finite Abel summation give the real-endpoint prime-counting expansion through its residual coefficient 24. The same literal finite prime intervals carry the nonlinear Euler deficit estimates used by the real-image infimum limit.

**Theorem 1.1 (Theta remainder at every fixed log power).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.theta_error_log_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.theta_error_log_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, theta(x)-x is little-o of x/log(x)^N at real atTop, using the actual MediumPNT exponent 1/10 and the frozen psi-minus-theta transfer.

**Definition 1.2 (Four-term counting polynomial).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.countingPolynomial`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.countingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

countingPolynomial x is x*(1/log x + 1/log(x)^2 + 2/log(x)^3 + 6/log(x)^4).

**Theorem 1.3 (Four terms with residual coefficient 24).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-endpoint residual (primeCount x-countingPolynomial x)/(x/log(x)^5) tends to 24 atTop. The primeCount definition includes the floor endpoint and no separate pi hypothesis is introduced.

**Definition 1.4 (primeCount).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.primeCount`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.primeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real endpoint counting function is Nat.primeCounting at the natural floor of t, cast to the reals. The floor convention fixes all endpoint ties.

**Definition 1.5 (primeInterval).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.primeInterval`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.primeInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite interval consists of primes in the natural Ioc from floor(y) to floor(z), so it represents the strict lower and included upper real endpoints y<p<=z.

**Definition 1.6 (squareSum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.squareSum`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.squareSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite square sum is the sum of p^-2 over that literal prime interval, with no infinite-tail replacement.

**Definition 1.7 (logarithmicTail).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.logarithmicTail`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.logarithmicTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic Euler tail is the finite sum of -log(1-p^-2) on the same interval as the square sum.

**Theorem 1.8 (log deficit bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.log_deficit_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.log_deficit_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<=q<1, the pinned elementary logarithm inequalities give q<=-log(1-q)<=q/(1-q), including q=0.

**Theorem 1.9 (finite logarithmic tail squeeze).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.finite_logarithmic_tail_squeeze`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.finite_logarithmic_tail_squeeze` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y>1 and every real z, the logarithmic Euler tail lies between the square sum and squareSum/(1-y^-2). The strict lower endpoint supplies a uniform positive denominator; empty intervals remain covered.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.countingPolynomial`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.finite_logarithmic_tail_squeeze`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.log_deficit_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.logarithmicTail`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.primeCount`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.primeInterval`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.prime_counting_four_terms`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.squareSum`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.theta_error_log_power`
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
- Dependency: [D5/S3/Weil/PrimeNumberTheorem/MediumPNT](../../../Weil/PrimeNumberTheorem/MediumPNT.md)
