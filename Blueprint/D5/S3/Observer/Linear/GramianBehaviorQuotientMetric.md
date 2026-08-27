# Gramian Behavior-Quotient Metric

## Abstract

The observability Gramian metrizes the complete future-behavior quotient.

**Theorem 1.1 (Gramian zero distance is complete behavioral equivalence).**

$$\forall K \in Type, V \in Type, Y \in Type, T \in LinearMap\left(K, V, V\right), C \in LinearMap\left(K, V, Y\right), beta \in \mathbb{R}, x \in V, y \in V,\; RCLike\left(K\right) \land NormedAddCommGroup\left(V\right) \land InnerProductSpace\left(K, V\right) \land FiniteDimensional\left(K, V\right) \land NormedAddCommGroup\left(Y\right) \land InnerProductSpace\left(K, Y\right) \land FiniteDimensional\left(K, Y\right) \land 0 < beta < 1 \land \sqrt{beta} \left\lVert T \right\rVert < 1 \Rightarrow \left(\left(\forall n \in Nat,\; C\left(T^{n}\left(x\right)\right) = C\left(T^{n}\left(y\right)\right)\right) \Leftrightarrow re\left(inner\left(K, x - y, discountedObservabilityGramian\left(T, C, beta\right)\left(x - y\right)\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GramianBehaviorQuotientMetric.gramian_behavior_quotient_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evolution, readout, and discounted observability Gramian are the canonical imported linear-observer primitives.

For any two states, equality of every future readout is equivalent to zero real Gramian quadratic form on their difference. Thus the Gramian supplies a quadratic metric on the behavioral quotient.

## References

- Truth anchor: `D5/S3/Observer/Linear/GramianBehaviorQuotientMetric.gramian_behavior_quotient_metric`
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity](DiscountedObservabilityGramianPositivity.md)
