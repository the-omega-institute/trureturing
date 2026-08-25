# First Difference Power Law

## Abstract

The discounted discrete prediction distance is the power of the first differing readout.

**Theorem 1.1 (First difference determines discounted distance).**

$$\forall Y, O, [\operatorname{DecidableEq}\left(O\right)], tau: Y \to Y, q: Y \to O, gamma: \mathbb{R},\ (0 < gamma \leq 1)\Rightarrow\\{}\forall y, y'\in Y,\\{(\operatorname{orbitReadoutRelation}(tau, q, y, y')\Rightarrow \operatorname{discountedPredictionDistance}(tau, q, gamma, y, y') = 0)} \land\\{(\exists k\in \mathbb{N}, q(\operatorname{iterate}(tau, k, y)) \neq q(\operatorname{iterate}(tau, k, y'))\Rightarrow \operatorname{discountedPredictionDistance}(tau, q, gamma, y, y') = \operatorname{pow}(gamma, \operatorname{firstDifferenceIndex}(tau, q, y, y')))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw.first_difference_power_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relation R_q is equality of the q-readout at every iterate of the deterministic update tau. The distance is the existing discounted supremum using the discrete output discrepancy.

If two states are R_q-related, every discrepancy term is zero. If they are distinguishable, Nat.find supplies the minimum time at which the readouts differ; all earlier terms vanish and later powers of gamma are no larger, giving the displayed power exactly.

The theorem exposes both source clauses: zero distance on the relation and the first-difference power law for every separating witness.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw.first_difference_power_law`
- Dependency: [D5/S3/Observer/MetricGeometry/BellmanMaxEquation](../MetricGeometry/BellmanMaxEquation.md)
- Dependency: [D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric](../MetricGeometry/DiscretePredictionUltrametric.md)
