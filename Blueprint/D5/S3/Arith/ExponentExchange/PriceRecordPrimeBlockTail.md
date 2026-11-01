# Simultaneous Prime Block Exchange

## Abstract

A single actual predecessor exchange controls the weighted missing Euler tails of a finite block of primes at an arbitrary real price.

**Theorem 1.1 (Weighted missing tails share one removed prime layer).**

Lean statement: `D5/S3/Arith/ExponentExchange/PriceRecordPrimeBlockTail.price_record_prime_block_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/PriceRecordPrimeBlockTail.price_record_prime_block_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be any real number, m a positive natural number, and P a prime divisor of m. Assume the full predecessor record: for every positive natural number n < m, goldenResourceObjective(lambda,n) < goldenResourceObjective(lambda,m). Let S be any finite set of primes, Q its product (the empty product is 1), and k a natural number with k >= 1 and Q^k < P. Write a(q) = Nat.factorization(m,q), T(q) = OriginalEndpointPrimeTail.layerTail(m,q) = -log(1-(1/q)^(a(q)+1)), and G(P) = goldenLayerMarginal(P,a(P))*log(P).

Then sum over q in S of (1-(1/q)^k)*T(q), plus lambda*(log(P)-k*log(Q)), is strictly less than G(P), and G(P) <= 1/P. All logarithms use real casts. There is no nonempty-set assumption and no requirement that any q in S divides m: zero valuations are included. Positivity of lambda is not needed for this signed-price conclusion.

The proof uses the one actual integer n = (m/P)*Q^k, which is positive and strictly smaller than m. Since Q^k < P, P is absent from S. Removing P decreases its valuation by one and leaves every S valuation unchanged; inserting Q^k increases all those valuations by k simultaneously. The existing finite-support objective identity therefore expresses the total gain as one sum of local increments. The predecessor record is applied once to this n. The price correction is lambda*(log(P)-k*log(Q)); the removed P layer is paid only once.

For r = (1/q)^(a(q)+1) and s = (1/q)^k, logarithm concavity at 1-r and 1 gives -log(1-s*r) <= s*(-log(1-r)). Consequently the actual k-layer gain log(1-s*r)-log(1-r) is at least (1-s)*T(q). Summing these estimates in the exact simultaneous exchange proves the weighted inequality. The existing occupied-layer marginal bound then gives G(P) <= (1/P)^a(P) <= 1/P.

For the four primes in the support of 5040, take S = {2,3,5,7} and k = 1. If P > 210, the product condition holds. Since every T(q) is nonnegative and 1-1/q >= 1/2 on this set, their unweighted sum D4 satisfies D4 < 2/P - 2*lambda*log(P/210). For lambda > 0 this is strictly less than 2/P. The four tails share one removed-layer budget; summing four separate one-prime bounds would give 8/P. This application requires the same full predecessor record, and makes no assumption that the valuations equal those of 5040.

This is a bound conditional on a full predecessor record, with the actual Euler tails of that same integer. It assumes neither global colossal-abundance optimality nor initial prime support. It does not bound the complete prime tail unless that additional reduction is proved, and it asserts no all-integer Robin inequality or RH result. The result is a repository derivation using classical prime-benefit exchange ideas; no claim of literature novelty is made.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/PriceRecordPrimeBlockTail.price_record_prime_block_tail`
- Dependency: [D5/S3/Arith/ExponentExchange/PriceRecordMissingLayer](PriceRecordMissingLayer.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEndpointPrimeTail](../Robin/OriginalEndpointPrimeTail.md)
- Dependency: [D5/S3/Arith/Robin/PrimeValuation5040Bridge](../Robin/PrimeValuation5040Bridge.md)
