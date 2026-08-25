# Weighted Prediction Zero Kernel

## Abstract

Positive coordinate weights and discount identify zero prediction distance with orbit-readout agreement.

**Theorem 1.1 (Zero distance is dynamic indistinguishability).**

$$\operatorname{PositiveWeights}(J, w) \land 0< gamma \leq 1 \Rightarrow\\{}\forall x, y\in X,\\{}(\operatorname{DiscountedPredictionDistance}(F, J, w, q, gamma, x, y) = 0) \iff (\forall n\in N, \forall i\in J, \operatorname{Readout}(q, i, \operatorname{Iterate}(F, n, x)) = \operatorname{Readout}(q, i, \operatorname{Iterate}(F, n, y))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel.weighted_prediction_zero_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite observation budget J selects equality-valued coordinate readouts. Their static discrepancy is the largest selected positive weight whose two coordinate values differ.

The dynamic distance is the canonical discounted supremum of that coordinate discrepancy along the two update orbits. Positivity of every selected weight and every discount power makes a zero term equivalent to equality of the corresponding readouts.

The empty budget is included: its discrepancy is zero and its universal readout-agreement condition is vacuous.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel.weighted_prediction_zero_kernel`
- Dependency: [D5/S3/Observer/MetricGeometry/BellmanMaxEquation](../MetricGeometry/BellmanMaxEquation.md)
- Dependency: [D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric](../MetricGeometry/DiscretePredictionUltrametric.md)
