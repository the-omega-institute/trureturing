# Golden Resource Threshold Criterion

## Abstract

A positive integer maximizes the resource objective at a fixed positive price exactly when every unadopted boundary layer is below the price and every adopted boundary layer is above it, allowing equality.

**Definition 1.1 (Optimality at a fixed price).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; IsGoldenResourceOptimal\left(lambda, n\right) \Leftrightarrow \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow goldenResourceObjective\left(lambda, m\right) \le goldenResourceObjective\left(lambda, n\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.IsGoldenResourceOptimal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any real price lambda and natural n, the predicate compares n with every positive natural competitor m. Positivity of n and lambda is imposed by the criterion below.

**Theorem 1.2 (A profitable next layer gives a better integer).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N}, p \in \mathbb{N},\; \left(0 < lambda \land \left(1 \le n \land \left(Prime\left(p\right) \land lambda < goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right)\right)\right)\right) \Rightarrow goldenResourceObjective\left(lambda, n\right) < goldenResourceObjective\left(lambda, n \cdot p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.golden_resource_strict_improvement_of_marginal_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive lambda, positive n, and a prime p, a next-layer marginal strictly greater than lambda makes n times p strictly better than n. The proof places both objectives on the same finite prime support, cancels the unchanged directions, and computes the remaining gain as log p times marginal minus price. This is the named witness consumed by the necessary upper threshold in the criterion.

**Theorem 1.3 (Fixed-price global optimality and boundary thresholds).**

$$\forall lambda \in \mathbb{R}, n \in \mathbb{N},\; \left(0 < lambda \land 1 \le n\right) \Rightarrow \left(IsGoldenResourceOptimal\left(lambda, n\right) \Leftrightarrow \left(\left(\forall p \in \mathbb{N},\; Prime\left(p\right) \Rightarrow goldenLayerMarginal\left(p, factorization\left(n, p\right) + 1\right) \le lambda\right) \land \left(\forall p \in \mathbb{N},\; \left(Prime\left(p\right) \land p \mid n\right) \Rightarrow lambda \le goldenLayerMarginal\left(p, factorization\left(n, p\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.golden_resource_optimal_iff_layer_thresholds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For lambda greater than zero and n at least one, optimality is equivalent to the following two conditions. For every prime p, the marginal at exponent factorization n p plus one is at most lambda. For each prime p dividing n, lambda is at most the marginal at exponent factorization n p. Equality is retained.

Necessity compares n with n times p and, for adopted directions, with n divided by p. Sufficiency applies the frozen one-prime threshold theorem termwise after expressing n and an arbitrary positive competitor on the union of their finite prime supports.

This slice uses a fixed price. It does not define L or U, establish their extrema, identify a colossally abundant predicate with a nonempty price interval, reduce absent-prime checks to the smallest missing prime, or classify all ties at critical prices.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.IsGoldenResourceOptimal`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.golden_resource_optimal_iff_layer_thresholds`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.golden_resource_strict_improvement_of_marginal_gt`
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../GoldenResourceObjectiveFactorization.md)
