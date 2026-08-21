# Discounted Prediction Pseudometric

## Abstract

Discounted prediction distance is a bounded pseudometric.

**Theorem 1.1 (Discounted prediction distance is a bounded pseudometric).**

$$\operatorname{BoundedOutputPseudometric}(q, D) \land 0< gamma \leq 1 \Rightarrow\\\forall y, y', y''\in Y,\ {0\leq \operatorname{DiscountedDistance}(y, y') \leq D} \land\\\operatorname{DiscountedDistance}(y, y) = 0 \land\\\operatorname{DiscountedDistance}(y, y') = \operatorname{DiscountedDistance}(y', y) \land\\\operatorname{DiscountedDistance}(y, y') \leq \operatorname{DiscountedDistance}(y, y'') + \operatorname{DiscountedDistance}(y'', y').$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric.discounted_prediction_pseudometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output carrier has its canonical pseudometric, and every output distance is bounded by D. A deterministic update and readout are combined with a discount factor gamma in (0, 1].

The discounted prediction distance is the supremum of gamma to the time k multiplied by the output distance after k updates. The proof uses the bounded real supremum API and the pseudometric laws pointwise along each orbit.

All four source clauses remain public: nonnegativity and the global bound, zero on the diagonal, symmetry, and the triangle inequality.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric.discounted_prediction_pseudometric`
- Dependency: [D5/S3/Observer/MetricGeometry/BellmanMaxEquation](../MetricGeometry/BellmanMaxEquation.md)
