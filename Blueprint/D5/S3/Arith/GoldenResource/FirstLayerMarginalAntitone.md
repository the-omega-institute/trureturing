# First-Layer Marginal Antitonicity and Finite Maximum

## Abstract

Prime antitonicity reduces the upper layer price to an explicit finite maximum.

**Theorem 1.1 (The successor-logarithm identity).**

$$\forall x \in \mathbb{R},\; 1 < x \Rightarrow \frac{log\left(x + 1\right)}{log\left(x\right)} = 1 + \frac{log\left(1 + \frac{1}{x}\right)}{log\left(x\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.log_add_one_div_log_eq_one_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x > 1, factor x + 1 as x(1 + 1/x). Additivity of the logarithm separates the quotient into one plus the first-layer term.

**Theorem 1.2 (Normalization of the first golden layer).**

$$\forall p \in \mathbb{N},\; Prime\left(p\right) \Rightarrow goldenLayerMarginal\left(p, 1\right) = \frac{log\left(1 + \frac{1}{p}\right)}{log\left(p\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.golden_layer_marginal_one_eq_log_one_add_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At layer one, the ratio in goldenLayerMarginal simplifies to 1 + 1/p, so the marginal is exactly the normalized logarithmic quotient.

**Theorem 1.3 (Strict decrease across primes).**

$$\forall p \in \mathbb{N}, q \in \mathbb{N},\; \left(Prime\left(p\right) \land \left(2 \le p \land \left(Prime\left(q\right) \land p < q\right)\right)\right) \Rightarrow \frac{log\left(q + 1\right)}{log\left(q\right)} < \frac{log\left(p + 1\right)}{log\left(p\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.log_add_one_div_log_strictAnti_of_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For primes with 2 <= p < q, the successor-logarithm quotient at q is strictly smaller than at p. The common additive term from the splitting identity leaves the strictly decreasing first-layer marginals.

**Theorem 1.4 (The upper price is a finite maximum).**

$$\forall n \in \mathbb{N}, q \in \mathbb{N},\; \left(1 \le n \land IsLeast\left(\{p: \mathbb{N} \mid Prime\left(p\right) \land \left(\neg p \mid n\right)\}, q\right)\right) \Rightarrow goldenUpperPrice\left(n\right) = \max_{p \in insert\left(q, primeFactors\left(n\right)\right)} goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.golden_upper_price_eq_finite_max_of_isLeast_missing_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be the least prime not dividing a positive integer n. The upper layer price equals the maximum of the next-layer marginals over q together with the prime factors of n. Every other prime has first layer marginal at most that of q, so no further prime changes the maximum.

**Theorem 1.5 (The finite maximum without a supplied least prime).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{N},\; IsLeast\left(\{p: \mathbb{N} \mid Prime\left(p\right) \land \left(\neg p \mid n\right)\}, q\right) \land goldenUpperPrice\left(n\right) = \max_{p \in insert\left(q, primeFactors\left(n\right)\right)} goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.golden_upper_price_eq_finite_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least prime not dividing n exists for every positive n, so the finite maximum needs no such prime as an input. Producing it here states the reduction of the upper price outright rather than relative to a caller.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.golden_layer_marginal_one_eq_log_one_add_inv`
- Truth anchor: `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.golden_upper_price_eq_finite_max`
- Truth anchor: `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.golden_upper_price_eq_finite_max_of_isLeast_missing_prime`
- Truth anchor: `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.log_add_one_div_log_eq_one_add`
- Truth anchor: `D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.log_add_one_div_log_strictAnti_of_prime`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval](GoldenResourcePriceInterval.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime](GoldenSmallestMissingPrime.md)
