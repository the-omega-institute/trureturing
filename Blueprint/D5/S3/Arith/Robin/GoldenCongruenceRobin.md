# Strict Robin for the Complete 5040 Power-Congruence Branch

## Abstract

Strict Robin holds throughout the 5040 divisibility and power-congruence branch, without an upper bound on the number of distinct prime factors.

**Theorem 1.1 (Strict Robin without a prime-count hypothesis).**

Lean statement: `D5/S3/Arith/Robin/GoldenCongruenceRobin.robin_of_modEq_2241`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenCongruenceRobin.robin_of_modEq_2241` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n > 5040 such that 5040 divides n and 3^n is congruent to 2241 modulo n, sigma(1,n)/n is strictly less than exp(gamma)*log(log(n)). Residual prime exponents and the number of distinct residual primes are unrestricted.

The existing shape theorem forces 4 <= v_2(n) <= 6, 2 <= v_3(n) <= 3 and v_5(n) = v_7(n) = 1. Their local divisor-sum defects give sigma(1,n)/n <= (2032/2205)*n/phi(n). The congruence also excludes the ten primes from 11 through 43. Their omitted Euler factors multiply to 3511517184000/5663533044013, giving the combined coefficient c = 3236010393600/5663533044013.

Suppose strict Robin fails. The existing thirty-nine-prime result then gives n >= 5040*47^36. Rational logarithm certificates give L = log(log(n)) > 4.99 and y = 2*log(n) >= 286. The elementary Mertens envelope bounds the full small-prime product by exp(gamma)*log(y)*exp(1.9/log(y)). The logarithmic budget for large prime divisors sharpens their product bound to exp(log(n)/((y-1)*log(y))).

Since log(n) >= 143, log(n)/(y-1) <= 0.51. Also 0.69 < log(2) < 0.694 and log(y) = L + log(2). Combining the two products and the omitted factors gives sigma(1,n)/(n*exp(gamma)*L) <= c*(1+0.694/L)*exp(2.41/(L+0.69)) < 1 for L >= 4.99. The last strict inequality uses a certified logarithmic lower bound proving exp(241/568) < 1.53 and an exact rational margin. This contradicts the assumed failure and closes the whole stated branch.

The new numerical input is the same-delivery elementary Mertens supplier, including its direct rational weighted-prime sum and proved infinite tail. No Rosser-Schoenfeld table or colossally abundant finite computation is assumed.

This restricted ordinary range is already covered by Hertlein's small-valuation Robin criteria (Integers 18 (2018), A71, Theorems 1 and 2) and Axler's strengthened criteria (arXiv:2110.13478v3, Theorem 1.4). The contribution is the checked elementary library proof chain, not a new ordinary Robin range. The theorem retains both divisibility and power-congruence hypotheses; it does not prove strict Robin for every integer greater than 5040 or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/GoldenCongruenceRobin.robin_of_modEq_2241`
- Dependency: [D5/S3/Arith/Robin/ElevenSmooth](ElevenSmooth.md)
- Dependency: [D5/S3/Arith/Robin/GoldenResidualFive](GoldenResidualFive.md)
- Dependency: [D5/S3/Arith/Robin/MertensExplicitEnvelope](MertensExplicitEnvelope.md)
