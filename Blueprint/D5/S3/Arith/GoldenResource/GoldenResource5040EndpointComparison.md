# Golden Resource Endpoint Comparisons at 5040

## Abstract

A single prime layer determines the two adjacent objective comparisons at 5040.

**Theorem 1.1 (The exact objective change from adding one prime layer).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N}, p \in \mathbb{N},\; \left(1 \le n \land Prime\left(p\right)\right) \Rightarrow goldenResourceObjective\left(lambda, n \cdot p\right) - goldenResourceObjective\left(lambda, n\right) = (goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right) - lambda) \cdot log\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison.golden_resource_objective_single_layer_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real price lambda, positive natural number n, and prime p, multiplication of n by p changes the objective by the next layer marginal minus lambda, multiplied by log p. Positivity of n is an explicit hypothesis.

The proof applies the frozen finite-support decomposition to n and n times p on one common support. Prime factorization changes only at p; all other local differences vanish. The remaining difference is evaluated using exact logarithm identities.

**Theorem 1.2 (The two adjacent comparisons beyond the price interval).**

$$\forall lambda \in \mathbb{R},\; \left(\frac{log\left(\frac{31}{30}\right)}{log\left(2\right)} \le lambda \Rightarrow goldenResourceObjective\left(lambda, 5040\right) \le goldenResourceObjective\left(lambda, 2520\right)\right) \land \left(lambda \le \frac{log\left(\frac{12}{11}\right)}{log\left(11\right)} \Rightarrow goldenResourceObjective\left(lambda, 5040\right) \le goldenResourceObjective\left(lambda, 55440\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison.golden_resource_5040_endpoint_comparisons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a price at least log(31/30) divided by log 2, the objective at 2520 is at least the objective at 5040. At a price at most log(12/11) divided by log 11, the objective at 55440 is at least the objective at 5040. The comparisons include their endpoints and are non-strict.

This companion consumes the single-layer delta at n = 2520, p = 2 and n = 5040, p = 11. The exact boundary marginals are those of layer (2,4) and layer (11,1). The dependency direction is endpoint comparisons to single-layer delta.

The statement covers only these adjacent comparisons. The previously frozen strict-interval sufficiency result remains upstream. Global endpoint maximality, numerical decimal bounds, and comparisons with the continuous allocation model are not asserted here.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison.golden_resource_5040_endpoint_comparisons`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison.golden_resource_objective_single_layer_delta`
- Dependency: [D5/S3/Arith/GoldenResource5040PriceInterval](../GoldenResource5040PriceInterval.md)
