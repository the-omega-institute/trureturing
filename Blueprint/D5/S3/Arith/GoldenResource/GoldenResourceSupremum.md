# Golden Resource Supremum

## Abstract

At positive prices the resource supremum equals the finite sum of positive layer gains.

**Theorem 1.1 (The objective at the minimal-count configuration).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; \left(0 < lambda \land \left(1 \le n \land \left(\forall p \in \mathbb{N},\; factorization\left(n, p\right) = optimalLayerCount\left(lambda, p\right)\right)\right)\right) \Rightarrow goldenResourceObjective\left(lambda, n\right) = \sum_{(p,k)\in\{(p,k): \mathbb{N}\times\mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\}} log\left(p\right) \cdot (goldenLayerMarginal\left(p, k\right) - lambda)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.objective_at_optimal_eq_positive_part_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive price and a positive integer realizing optimalLayerCount at every natural p, the objective equals the sum of log p times the net marginal over all strictly profitable prime-layer pairs. The frozen count specification supplies such an integer. The proof telescopes the public single-layer delta along each prime power, then regroups the finite active-pair set by prime. This is the value identity used by the supremum theorem.

**Theorem 1.2 (The exact unconstrained optimal value).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow sSup\left(\{x: \mathbb{R} \mid \exists n \in \mathbb{N},\; 1 \le n \land goldenResourceObjective\left(lambda, n\right) = x\}\right) = \sum_{(p,k)\in\{(p,k): \mathbb{N}\times\mathbb{N} \mid 1 \le k \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, k\right)\right)\}} log\left(p\right) \cdot (goldenLayerMarginal\left(p, k\right) - lambda)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supremum ranges over objective values of all positive integers. The frozen count specification supplies a greatest element, so this supremum is attained and equals the objective evaluated in the preceding theorem.

The sum is indexed by the finite set of all pairs (p,k) with p prime, k at least one, and marginal strictly above lambda. Thus each included net marginal equals its positive part; all excluded positive-index prime layers have zero positive part. This finite support presentation expresses the positive-part double sum. The hypothesis lambda greater than zero is essential. No claim about nonpositive prices or the RH boundary is made.

**Theorem 1.3 (Equality-price layers preserve the objective).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N}, p \in \mathbb{N},\; \left(1 \le n \land \left(Prime\left(p\right) \land goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right) = lambda\right)\right) \Rightarrow goldenResourceObjective\left(lambda, n \cdot p\right) = goldenResourceObjective\left(lambda, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_objective_eq_of_layer_price` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real price, positive integer n and prime p, if the next p-layer has marginal equal to the price, n and n times p have equal objectives. Reading the equality in reverse also describes removal of that layer. This companion is a direct application of the frozen single-layer delta to the equality-price clause.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_objective_eq_of_layer_price`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.objective_at_optimal_eq_positive_part_sum`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](GoldenResourceOptimalLayerCount.md)
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../GoldenResourceObjectiveFactorization.md)
