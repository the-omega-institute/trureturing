# Prime expansion and second-threshold budget

## Abstract

Prime-counting coefficients and the residual budget at the second distinct-prime threshold.

**Definition 1.1 (Three-term counting polynomial).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.countingThreeTerms`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.countingThreeTerms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is P/log(P)+P/log(P)^2+2P/log(P)^3. The prime count uses the natural floor of the real endpoint P.

**Theorem 1.2 (Three-term prime-counting expansion).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_three_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_three_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After subtracting the three-term polynomial, division by P/log(P)^4 gives limit six as P tends to positive infinity. This follows from the existing four-term expansion with its next residual coefficient twenty-four.

**Theorem 1.3 (Uniform eventual counting error).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all sufficiently large real P, the absolute difference between the prime count and P/log(P) is at most 3P/log(P)^2. The same bound applies at every endpoint beyond a single fixed threshold.

**Definition 1.4 (Second-threshold budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The budget is P-theta(P)+(primeCount(P)-P/log(P)-P/log(P)^2)*log(P). It retains the exact prime-counting and Chebyshev terms before normalization.

**Theorem 1.5 (Exact cancellation and residual coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The budget divided by P/log(P)^2 tends to two. The first two prime-counting terms cancel the threshold exactly; the third coefficient supplies two, while the Chebyshev error vanishes on this scale.

These estimates support an upper bound for integers whose number of distinct prime factors exceeds the second threshold. A matching lower bound is not established here.

**Theorem 1.6 (Uniform central prime-counting error).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.central_prime_counting_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.central_prime_counting_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large real P and every real t in the closed interval [P/2,2P], the absolute difference between primeCount(t) and t/log(P) is at most 28P/log(P)^2. The prime count includes primes at the floored real endpoint.

The constant density uses the same central endpoint P throughout the interval. The bound combines the uniform eventual error at t with the change from log(t) to log(P). It supports the moving prime-weight upper estimate; no matching lower bound for the second distinct-prime threshold is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.central_prime_counting_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.countingThreeTerms`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_error_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_three_terms`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](../../PriceRecord/QuantitativePrimeAbel.md)
