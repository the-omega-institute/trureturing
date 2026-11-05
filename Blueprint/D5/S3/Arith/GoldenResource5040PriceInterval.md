# Golden Resource 5040 Price Interval

## Abstract

Every price strictly between the two adjacent layer thresholds makes 5040 the unique maximizer of the golden resource objective.

**Definition 1.1 (The existing 5040 exponent profile).**

Lean statement: `D5/S3/Arith/GoldenResource5040PriceInterval.targetExponent5040`

*Formalization.* `D5/S3/Arith/GoldenResource5040PriceInterval.targetExponent5040` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original exponent profile is exposed in place for the boundary computation in ActualRobinInterval. It assigns 4, 2, 1 and 1 to the primes 2, 3, 5 and 7, and zero elsewhere. Its body is unchanged.

**Lemma 1.2 (An existing rational lower comparison for a layer price).**

Lean statement: `D5/S3/Arith/GoldenResource5040PriceInterval.one_div_nat_lt_golden_layer_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource5040PriceInterval.one_div_nat_lt_golden_layer_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, a positive layer and positive natural k, the stated strict power comparison gives 1/k < goldenLayerMarginal p a. The original logarithm proof is reused by the exact boundary computation; public visibility does not add a new estimate.

**Lemma 1.3 (An existing rational upper comparison for a layer price).**

Lean statement: `D5/S3/Arith/GoldenResource5040PriceInterval.golden_layer_marginal_lt_one_div_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource5040PriceInterval.golden_layer_marginal_lt_one_div_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The opposite strict power comparison gives goldenLayerMarginal p a < 1/k under the original prime, positive-layer and positive-k hypotheses. The unchanged proof supplies the omitted-layer comparisons in ActualRobinInterval's boundary computation.

**Lemma 1.4 (The existing target profile is the actual factorization).**

Lean statement: `D5/S3/Arith/GoldenResource5040PriceInterval.target_exponent_eq_factorization_5040`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource5040PriceInterval.target_exponent_eq_factorization_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original proof identifies targetExponent5040 p with the factorization of 5040 at every natural p. It remains at this owner and is reused directly by the original optimizer boundary proof. Only its visibility has changed.

**Theorem 1.5 (Original generic strict-threshold uniqueness).**

$$\forall p \in \mathbb{N}, a \in \mathbb{N}, lambda \in \mathbb{R},\; (Prime\left(p\right) \land \left(goldenLayerMarginal\left(p, a + 1\right) < lambda \land \left(a = 0 \lor lambda < goldenLayerMarginal\left(p, a\right)\right)\right)) \Rightarrow \left(\forall b \in \mathbb{N},\; (goldenPrimeLocalObjective\left(lambda, p, b\right) \le goldenPrimeLocalObjective\left(lambda, p, a\right) \land \left(goldenPrimeLocalObjective\left(lambda, p, b\right) = goldenPrimeLocalObjective\left(lambda, p, a\right) \Leftrightarrow b = a\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource5040PriceInterval.golden_prime_local_objective_unique_maximal_of_strict_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing generic proof is exposed in place for ActualReservePrimeMask. For any real price and actual prime, strict upper and lower thresholds make the chosen exponent maximal, with equality exactly at that exponent. The lower condition allows exponent zero. The theorem is generic despite the 5040 filename; its original proof is unchanged.

**Theorem 1.6 (The open threshold interval suffices for unique optimality).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; (\frac{log\left(\frac{12}{11}\right)}{log\left(11\right)} < lambda \land \left(lambda < \frac{log\left(\frac{31}{30}\right)}{log\left(2\right)} \land 1 \le n\right)) \Rightarrow (goldenResourceObjective\left(lambda, n\right) \le goldenResourceObjective\left(lambda, 5040\right) \land \left(goldenResourceObjective\left(lambda, n\right) = goldenResourceObjective\left(lambda, 5040\right) \Leftrightarrow n = 5040\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda lie strictly above log(12/11)/log(11) and strictly below log(31/30)/log(2). For every positive natural number n, the golden resource objective at n is at most its value at 5040, and equality holds exactly when n is 5040.

The proof identifies the upper endpoint with the adopted layer (2,4) and the lower endpoint with the first omitted layer (11,1). Strict decay within each prime and a uniform bound for larger primes propagate these comparisons to every adopted and omitted layer. Strict local threshold maximality is then summed over the union of the prime supports of n and 5040.

This theorem proves only the sufficient open-interval direction. It does not prove necessity outside the interval, classify endpoint ties, supply decimal approximations, compare classical sequences, or interpret the separate price lambda = 0.04 example.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.golden_layer_marginal_lt_one_div_nat`
- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.golden_prime_local_objective_unique_maximal_of_strict_threshold`
- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval`
- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.one_div_nat_lt_golden_layer_marginal`
- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.targetExponent5040`
- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.target_exponent_eq_factorization_5040`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](GoldenLocalThreshold.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](GoldenResourceObjectiveFactorization.md)
