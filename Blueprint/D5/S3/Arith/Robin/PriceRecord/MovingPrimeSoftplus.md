# The normalized prime softplus sum

## Abstract

Moving softplus weights on primes.

**Definition 1.1 (Moving softplus weight).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.weight`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At t the weight is log(1 + exp(-s |log(t/P)|)), where P is the real center and s is the scale.

**Theorem 1.2 (The moving prime sum tends to the Fermi mass).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.prime_softplus_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.prime_softplus_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any real a > 0 and 0 < C1 <= C2. Let s be an arbitrary real function with C1(log P)^a <= s(P) <= C2(log P)^a for all sufficiently large real P. The sum of the actual weights over primes is eventually absolutely summable. Dividing the sum by P/(s(P) log P) gives a limit of pi^2/6 as P tends to infinity.

Finite Abel summation on each side of P compares the sum weighted by log p on (P/2, 2P] with the Lebesgue integral of the weight. The error is at most six times log(2) times the uniform theta discrepancy. Any integer log power N > a in the theta estimate makes this error negligible after scaling by s(P)/P. On this interval the difference between log p and log P is bounded by log(2), allowing the logarithmic factors to be removed.

The substitution t = P exp(u/s(P)) gives dominated convergence to the even softplus profile. Integration by parts identifies its half-line mass with the Fermi integral at exponent two, whose exact value is pi^2/12. The two far tails together are bounded by 5 P exp(-s(P) log(2)) once P and s(P) are at least two. The same upper tail comparison gives absolute summability.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.prime_softplus_asymptotic`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus.weight`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FirstPrimePrefixLocalization](FirstPrimePrefixLocalization.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
- Dependency: [D5/S3/Weil/ZetaBridge/FermiMellin](../../../Weil/ZetaBridge/FermiMellin.md)
