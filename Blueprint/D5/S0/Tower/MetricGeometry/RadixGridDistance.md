# Radix Grid Distance

## Abstract

Radix rounding distance equals metric distance to the radix grid.

**Theorem 1.1 (Rounding realizes radix-grid distance).**

$$\forall b \in N, Q \in N,\; b \ne 0 \Rightarrow \left(\forall x \in R,\; \operatorname{radixDistance}\left(b, Q, x\right) = \operatorname{infDist}\left(x, \operatorname{radixGrid}\left(b, Q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/RadixGridDistance.radixDistance_eq_infDist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero radix and every level, scaling and rounding to a nearest integer gives exactly the metric infimum distance from the point to the corresponding radix grid.

The lower bound applies Metric.le_infDist and round_le to every grid point. The rounded integer supplies a grid member for the reverse bound through Metric.infDist_le_dist_of_mem.

**Lemma 1.2 (Binary point distances have the integer numerator formula).**

$$\forall Q \in N,\; \forall m \in Z,\; \left|\frac{1}{3} - \frac{m}{2^{Q}}\right| = \frac{\left|2^{Q} - 3 \cdot m\right|}{3 \cdot 2^{Q}}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_point_distance_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every binary level and integer grid index m, the pointwise distance from one third to m divided by two to that level is the absolute integer residual divided by three times the scale.

**Lemma 1.3 (Binary powers are nonzero modulo three).**

$$\forall Q \in N,\; \operatorname{mod}\left(2^{Q}, 3\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_pow_mod_three_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a power of two were zero modulo three, primality would force three to divide two. Pinned mathlib supplies the exact prime-divides-a-power implication used for that contradiction.

**Lemma 1.4 (The binary integer residual minimum is one).**

$$\forall Q \in N,\; \left(\exists m \in Z,\; \left|2^{Q} - 3 \cdot m\right| = 1\right) \land \left(\forall m \in Z,\; \left|2^{Q} - 3 \cdot m\right| \ge 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_integer_residual_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An induction constructs an integer index whose residual is plus or minus one. If any residual vanished, the preceding nonzero modulo three result would be contradicted, so every absolute residual is at least one.

**Theorem 1.5 (Binary one third has exact distance to the actual grid).**

$$\forall Q \in N,\; Q \ge 1 \Rightarrow \left(2^{Q} \cdot \operatorname{infDist}\left(\frac{1}{3}, \operatorname{radixGrid}\left(2, Q\right)\right) = \frac{1}{3} \land \operatorname{infDist}\left(\frac{1}{3}, \operatorname{radixGrid}\left(2, Q\right)\right) = \frac{1}{3 \cdot 2^{Q}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_grid_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive binary level, two to the level times the metric infimum distance from one third to the radix grid is one third, and the unscaled distance is one divided by three times that power of two.

This applies the frozen binary arm computation through the public rounding-to-grid bridge; it does not restate or reprove that frozen theorem.

**Theorem 1.6 (All binary constant-arm clauses).**

$$\forall Q \in N,\; Q \ge 1 \Rightarrow \left(\operatorname{Coprime}\left(3, 2\right) \land \left(\left(\forall m \in Z,\; \left|\frac{1}{3} - \frac{m}{2^{Q}}\right| = \frac{\left|2^{Q} - 3 \cdot m\right|}{3 \cdot 2^{Q}}\right) \land \left(\operatorname{mod}\left(2^{Q}, 3\right) \ne 0 \land \left(\left(\exists m \in Z,\; \left|2^{Q} - 3 \cdot m\right| = 1\right) \land \left(\left(\forall m \in Z,\; \left|2^{Q} - 3 \cdot m\right| \ge 1\right) \land \left(2^{Q} \cdot \operatorname{infDist}\left(\frac{1}{3}, \operatorname{radixGrid}\left(2, Q\right)\right) = \frac{1}{3} \land \operatorname{infDist}\left(\frac{1}{3}, \operatorname{radixGrid}\left(2, Q\right)\right) = \frac{1}{3 \cdot 2^{Q}}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_constant_arm_clauses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive level, one declaration packages the source proposition's coprimality, pointwise numerator, nonzero residue, exact residual minimum, normalized distance, and unscaled distance clauses.

The proof applies the pinned coprime-two characterization and each preceding public declaration. The radix-grid set itself is the frozen radixGrid definition imported from ConstantArms.

## References

- Truth anchor: `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_constant_arm_clauses`
- Truth anchor: `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_grid_distance`
- Truth anchor: `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_integer_residual_minimum`
- Truth anchor: `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_point_distance_formula`
- Truth anchor: `D5/S0/Tower/MetricGeometry/RadixGridDistance.binary_pow_mod_three_ne_zero`
- Truth anchor: `D5/S0/Tower/MetricGeometry/RadixGridDistance.radixDistance_eq_infDist`
- Dependency: [D5/S0/Tower/ConstantArms](../ConstantArms.md)
