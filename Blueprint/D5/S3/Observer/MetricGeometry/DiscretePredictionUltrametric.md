# Discrete Prediction Ultrametric

## Abstract

Discrete-output prediction distance satisfies the strong triangle inequality.

**Theorem 1.1 (Discrete prediction distance obeys the strong triangle inequality).**

$$\forall \gamma\in(0, 1], \forall y, y', z\in Y,\ d_{\gamma}(y, z) \leq \max(d_{\gamma}(y, y'), d_{\gamma}(y', z)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric.discounted_prediction_distance_strong_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a deterministic update and a readout into a discrete output type. The output discrepancy is zero when two outputs agree and one otherwise. For a discount factor gamma in (0, 1], the prediction distance is the supremum over update times of the discounted output discrepancy.

The discrete discrepancy obeys the strong triangle inequality at each time. Nonnegative discount powers preserve that inequality. Boundedness by one supplies the conditionally complete suprema, and moving the pointwise maximum through the supremum proves the displayed law.

Loogle found the exact ciSup_sup_eq and mul_max_of_nonneg declarations used in the proof. LeanSearch returned the generic ultrametric interfaces and a fixed half-discount sequence metric, but no theorem for this arbitrary-discount observer distance. Repository and formalization-record searches found no duplicate.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric.discounted_prediction_distance_strong_triangle`
