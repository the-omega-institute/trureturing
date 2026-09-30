# Sharp Divisor-Count Bound

## Abstract

A sharp cubic-root estimate for the number of positive divisors.

Write tau(j) for the cardinality of the positive divisors of j.

**Theorem 1.1 (Cubic-root bound and equality case).**

$$(\forall j \in \mathbb{N}, 0 < j \Rightarrow \operatorname{tau}\left(j\right) \le 8 \cdot {\frac{3}{35}}^{\frac{1}{3}} \cdot {j}^{\frac{1}{3}} < 4 \cdot {j}^{\frac{1}{3}}) \land \operatorname{tau}\left(2520\right) = 8 \cdot {\frac{3}{35}}^{\frac{1}{3}} \cdot {2520}^{\frac{1}{3}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TauCubeRootBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive j, factorization expresses tau(j) as the product of one plus each prime exponent. Cubing these factors gives sharp local costs 8, 3, 8/5, and 8/7 at primes 2, 3, 5, and 7, respectively; every larger prime has cost one. A decreasing consecutive quotient extends the finite base checks to all exponents. Their product is 1536/35, so 35 tau(j)^3 <= 1536 j. Taking nonnegative cube roots yields the first bound. Since 3/35 < 1/8, its coefficient is strictly below four. At j = 2520 = 2^3 3^2 5 7, the divisor count is 48 and every local estimate is an equality.

## References

- Truth anchor: `D5/S3/Factorization/TauCubeRootBound.result`
