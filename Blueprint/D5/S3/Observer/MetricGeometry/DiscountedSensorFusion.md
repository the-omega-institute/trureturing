# Discounted Sensor-Fusion Distance

## Abstract

Discounted sensor-fusion distance is the maximum of its component distances.

**Theorem 1.1 (Discounted sensor-fusion distance is the component maximum).**

$$\forall gamma\in(0, 1], \forall y, y'\in Y,\ d_{gamma}^{12}(y, y') = \max(d_{gamma}^{1}(y, y'), d_{gamma}^{2}(y, y')).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/DiscountedSensorFusion.discounted_sensor_fusion_distance_eq_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two sensors observe the same updated state and let each sensor's real-valued discrepancy be nonnegative and uniformly bounded. For a discount factor gamma in (0, 1], define each component distance as the supremum over update times of gamma to that time times the component discrepancy. Define the fused discrepancy pointwise as the maximum of the two component discrepancies.

Each discounted component sequence is bounded above by its supplied discrepancy bound. Nonnegativity of every power of gamma lets scalar multiplication distribute across the pointwise maximum. The imported conditionally complete lattice identity ciSup_sup_eq then moves that maximum outside the indexed supremum and gives the equality.

Loogle found the exact ciSup_sup_eq and mul_max_of_nonneg declarations, and the proof imports and applies them. LeanSearch returned related supremum declarations but no full-statement match; repository and formalization-record searches found no duplicate.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/DiscountedSensorFusion.discounted_sensor_fusion_distance_eq_max`
