# Golden Resource Price Interval

## Abstract

The best unadopted prime layer has an attained positive price. Comparing it with the worst adopted layer characterizes existence of a common optimal price.

**Lemma 1.1 (Positive prime-layer marginals).**

Lean statement: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.marginal_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.marginal_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and natural layer a at least one, goldenLayerMarginal p a is positive. The original inverse-power and logarithm proof is retained at this owner. It supplies the two-adic seed in ActualGlobalBracketing.two_adic_seed and ActualGlobalBracketing.all_integer_bracketing, as well as this owner's golden_upper_price_attained and golden_upper_price_pos. This is reuse of existing mathematics through public visibility, not new escape content.

**Definition 1.2 (Upper layer price).**

$$\forall n \in \mathbb{N},\; goldenUpperPrice\left(n\right) = sSup\left(nextPrimeLayerValues\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.goldenUpperPrice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(n) is the real supremum of the set of next-layer marginals over all primes, with exponent factorization n p plus one. For positive n the supremum is attained, as proved below. The Lean API is named goldenUpperPrice.

**Definition 1.3 (Lower layer price).**

$$\forall n \in \mathbb{N},\; 1 < n \Rightarrow goldenLowerPrice\left(n\right) = min\left(adoptedPrimeLayerValues\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.goldenLowerPrice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n greater than one, U(n) is the minimum of the adopted-layer marginals over the finite nonempty set of prime divisors of n. For empty prime support, namely n equal to zero or one, goldenLowerPrice is defined to equal goldenUpperPrice. This real-valued boundary convention extends the existential criterion to one; it does not make the full set of prices at one a bounded interval.

**Definition 1.4 (Colossal abundance).**

$$\forall n \in \mathbb{N},\; IsColossallyAbundant\left(n\right) \Leftrightarrow \left(\exists lambda \in \mathbb{R},\; 0 < lambda \land IsGoldenResourceOptimal\left(lambda, n\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.IsColossallyAbundant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate asserts existence of a strictly positive real price at which n maximizes the frozen resource objective among all positive integers.

**Theorem 1.5 (A prime attains the best next-layer price).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists p \in \mathbb{N},\; Prime\left(p\right) \land \left(\forall r \in \mathbb{N},\; Prime\left(r\right) \Rightarrow goldenLayerMarginal\left(r, factorization\left(n, r\right) + 1\right) \le goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.golden_upper_price_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The next layer at prime two has positive marginal. The frozen uniform cutoff at that value leaves finitely many candidate primes. A maximum among these dominates the omitted tail, since every tail value is below the candidate at two. This constructs the preregistered witness for an arbitrary positive integer, without enumerating a fixed instance.

**Theorem 1.6 (The supremum is an attained maximum).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists p \in \mathbb{N},\; Prime\left(p\right) \land \left(goldenUpperPrice\left(n\right) = goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right) \land \left(\forall r \in \mathbb{N},\; Prime\left(r\right) \Rightarrow goldenLayerMarginal\left(r, factorization\left(n, r\right) + 1\right) \le goldenUpperPrice\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.golden_upper_price_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The attained maximum identifies the real supremum and supplies the upper bound for every next-layer marginal. The final criterion consumes this specification, so attainment is on its proof dependency path.

**Theorem 1.7 (The upper price is positive).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow 0 < goldenUpperPrice\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.golden_upper_price_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper price equals a positive prime-layer marginal. This gives the positive price selected in the sufficient direction of the criterion.

**Theorem 1.8 (Existence of a common price).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(IsColossallyAbundant\left(n\right) \Leftrightarrow goldenUpperPrice\left(n\right) \le goldenLowerPrice\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.colossally_abundant_iff_price_interval_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one, colossal abundance is equivalent to L(n) at most U(n). Necessity bounds L by an optimal price and bounds that price by every adopted-layer marginal. Sufficiency chooses the positive price L and applies the frozen fixed-price threshold criterion. Equality is kept. This slice does not separately state the characterization of every admissible price, reduce absent-prime comparisons to the smallest missing prime, or classify ties at critical parameters.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.IsColossallyAbundant`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.colossally_abundant_iff_price_interval_nonempty`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.goldenLowerPrice`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.goldenUpperPrice`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.golden_upper_price_attained`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.golden_upper_price_pos`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.golden_upper_price_spec`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.marginal_pos`
- Dependency: [D5/S3/Arith/GoldenPrimeLayerCofinite](../GoldenPrimeLayerCofinite.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion](GoldenResourceThresholdCriterion.md)
