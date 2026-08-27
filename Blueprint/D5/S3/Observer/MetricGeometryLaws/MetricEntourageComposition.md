# Metric Entourage Composition

## Abstract

Metric entourages compose within the entourage at the sum of radii.

**Theorem 1.1 (Metric entourage composition is bounded by the summed radius).**

$$\forall X: \operatorname{Type}, [\operatorname{PseudoMetricSpace}(X)], \forall epsilon, delta: Real,\ relationCompose(metricEntourage(epsilon), metricEntourage(delta)) \subseteq metricEntourage(epsilon + delta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/MetricEntourageComposition.metric_entourage_comp_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a pseudometric state carrier, the source entourage at radius epsilon consists of pairs whose distance is at most epsilon, and relation composition exposes an intermediate state.

If the first and second legs have bounds epsilon and delta, the metric triangle inequality bounds the composite leg by epsilon plus delta.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/MetricEntourageComposition.metric_entourage_comp_subset`
