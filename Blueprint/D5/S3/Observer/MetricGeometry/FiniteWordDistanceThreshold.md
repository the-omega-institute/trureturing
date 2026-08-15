# Finite Word Distance Threshold

## Abstract

Finite readout agreement is exactly a discrete prediction-distance threshold.

**Theorem 1.1 (Finite words are exactly discrete prediction balls).**

$$\forall \gamma\in (0, 1),\ \forall m\in \mathbb{N},\ \forall y, y'\in Y,\ (\forall k \leq m,\ q(\tau^{k}(y))=q(\tau^{k}(y'))) \Leftrightarrow d_{\gamma}(y, y') \leq \gamma^{m+1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/FiniteWordDistanceThreshold.finite_word_equivalent_iff_prediction_distance_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an update, a discrete readout, and a discount factor gamma strictly between zero and one. For every natural depth m and pair of states, agreement of the readouts at times zero through m is equivalent to their discounted prediction distance being at most gamma to the power m plus one.

The forward direction specializes the finite-readout fiber diameter bound to the zero-one output discrepancy. Conversely, a mismatch at time k at most m contributes gamma to the power k to the supremum. Strict geometric decay makes that contribution larger than gamma to the power m plus one, contradicting the threshold.

Loogle found no declaration named for this prediction distance, and the full-shape LeanSearch query returned only unrelated finite-product supremum metrics. Both searches identified the exact geometric decay result pow_lt_pow_right_of_lt_one₀. The proof also applies le_ciSup and the repository finite-word fiber diameter theorem; repository and formalization searches found no duplicate.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/FiniteWordDistanceThreshold.finite_word_equivalent_iff_prediction_distance_le`
- Dependency: [D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric](DiscretePredictionUltrametric.md)
- Dependency: [D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter](FiniteWordFiberDiameter.md)
