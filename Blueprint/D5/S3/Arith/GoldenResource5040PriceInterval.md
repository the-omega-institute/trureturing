# Golden Resource 5040 Price Interval

## Abstract

Every price strictly between the two adjacent layer thresholds makes 5040 the unique maximizer of the golden resource objective.

**Theorem 1.1 (The open threshold interval suffices for unique optimality).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; (\frac{log\left(\frac{12}{11}\right)}{log\left(11\right)} < lambda \land \left(lambda < \frac{log\left(\frac{31}{30}\right)}{log\left(2\right)} \land 1 \le n\right)) \Rightarrow (goldenResourceObjective\left(lambda, n\right) \le goldenResourceObjective\left(lambda, 5040\right) \land \left(goldenResourceObjective\left(lambda, n\right) = goldenResourceObjective\left(lambda, 5040\right) \Leftrightarrow n = 5040\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda lie strictly above log(12/11)/log(11) and strictly below log(31/30)/log(2). For every positive natural number n, the golden resource objective at n is at most its value at 5040, and equality holds exactly when n is 5040.

The proof identifies the upper endpoint with the adopted layer (2,4) and the lower endpoint with the first omitted layer (11,1). Strict decay within each prime and a uniform bound for larger primes propagate these comparisons to every adopted and omitted layer. Strict local threshold maximality is then summed over the union of the prime supports of n and 5040.

This theorem proves only the sufficient open-interval direction. It does not prove necessity outside the interval, classify endpoint ties, supply decimal approximations, compare classical sequences, or interpret the separate price lambda = 0.04 example.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](GoldenResourceObjectiveFactorization.md)
