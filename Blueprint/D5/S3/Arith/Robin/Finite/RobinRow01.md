# Robin1984 Row 01 at its original price

## Abstract

Unique optimizer at the original Robin1984 Row 01 price, a strict log margin reserve on log-height [22,36], and the finite Robin inequality through 321253732800.

Write sigma(n) for the sum of divisors of n and gamma for the Euler–Mascheroni constant. All logarithms are natural. For positive n the original objective at price q is G(q,n) = log(sigma(n)/n) - q log(n), and the Robin log margin is M(n) = gamma + log(log(log(n))) - log(sigma(n)/n).

The price and layer cutoffs [28, 6, 3, 2, 2, 2] come from Jonas Whidden's Robin1984 certificate robinFiniteRow01. Its original log-height window is [22117363/1000000, 35788699/1000000]. The pinned source is https://github.com/kimihiro64/Robin1984/blob/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Finite/Certificates/Row01.lean

**Definition 1.1 (Exact Row 01 price).**

Lean statement: `D5/S3/Arith/Robin/Finite/RobinRow01.row01Price`

*Formalization.* `D5/S3/Arith/Robin/Finite/RobinRow01.row01Price` (`✓ std3`).

*Citation.* Jonas Whidden (2026). *Robin1984: the actual Robin, colossally abundant and Lagarias equivalences*. URL: <https://github.com/kimihiro64/Robin1984/tree/acab1a31f31e0499518a4416b63281e0b4838f9c>.

*Commentary.*

The original price q is the positive real rational 2565510579241/250000000000000.

**Definition 1.2 (Row 01 integer).**

Lean statement: `D5/S3/Arith/Robin/Finite/RobinRow01.row01Integer`

*Formalization.* `D5/S3/Arith/Robin/Finite/RobinRow01.row01Integer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural integer N is 321253732800, the product 2^6 * 3^3 * 5^2 * 7 * 11 * 13 * 17 * 19 * 23.

**Theorem 1.3 (Unique optimizer at the original price).**

Lean statement: `D5/S3/Arith/Robin/Finite/RobinRow01.row01_optimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/RobinRow01.row01_optimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m >= 1, G(q,j) <= G(q,m) for all natural j >= 1 if and only if m = N. Exact rational logarithm bounds separate the marginal from q on both sides of each cutoff. Monotonicity in the base and layer gives strict signs on all prime layers, forcing the prime exponents of every optimizer.

**Theorem 1.4 (Strict log margin reserve).**

Lean statement: `D5/S3/Arith/Robin/Finite/RobinRow01.robin_log_margin_fixed_price_row01`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/RobinRow01.robin_log_margin_fixed_price_row01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n with 22 <= log(n) <= 36, the strict bound is 1/80 + G(q,N) - G(q,n) < M(n). This keeps the exact objective deficit at the original price. Rational bounds give a strict reserve at heights 22 and 36. Concavity of H ↦ gamma + log(log(H)) propagates the bound over the whole closed interval.

**Theorem 1.5 (Robin's inequality through 321253732800).**

Lean statement: `D5/S3/Arith/Robin/Finite/RobinRow01.original_robin_through_row01`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/RobinRow01.original_robin_through_row01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n with 5040 < n <= 321253732800, sigma(n) < exp(gamma) * n * log(log(n)) unconditionally. Whidden's nativeRobinInequality_finite_log gives the wider external range with log(n) < 74500. This derivation uses the original-price optimizer intervals. At each price at least q the optimizer endpoints divide N. Among endpoints above 5040, those with at most eight distinct prime factors satisfy the existing few-prime bound. Every remaining endpoint above 5040 is a multiple of 5354228880, which places its log-height in [22,36]. The strict reserve certifies those endpoints, and the original optimizer interval transfer then gives the inequality for every integer in the stated range.

## References

- Truth anchor: `D5/S3/Arith/Robin/Finite/RobinRow01.original_robin_through_row01`
- Truth anchor: `D5/S3/Arith/Robin/Finite/RobinRow01.robin_log_margin_fixed_price_row01`
- Truth anchor: `D5/S3/Arith/Robin/Finite/RobinRow01.row01Integer`
- Truth anchor: `D5/S3/Arith/Robin/Finite/RobinRow01.row01Price`
- Truth anchor: `D5/S3/Arith/Robin/Finite/RobinRow01.row01_optimal_iff`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Arith/Robin/ActualRobinInterval](../ActualRobinInterval.md)
