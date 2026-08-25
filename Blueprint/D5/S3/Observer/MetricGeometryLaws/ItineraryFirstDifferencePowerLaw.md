# Itinerary First Difference Power Law

## Abstract

Canonical complete itineraries determine the discounted discrete prediction distance.

**Theorem 1.1 (Itinerary first difference determines discounted distance).**

$$\forall Y, O, [\operatorname{DecidableEq}\left(O\right)], tau: Y \to Y, q: Y \to O, gamma: \mathbb{R},\ (0 < gamma \leq 1)\Rightarrow\\{}\forall y, y'\in Y,\\{(\operatorname{FutureIndistinguishable}(tau, q, y, y')\Rightarrow \operatorname{discountedPredictionDistance}(tau, q, discreteOutputDistance, gamma, y, y') = 0)} \land\\{(\exists k\in \mathbb{N}, q(\operatorname{iterate}(tau, k, y)) \neq q(\operatorname{iterate}(tau, k, y'))\Rightarrow \operatorname{discountedPredictionDistance}(tau, q, discreteOutputDistance, gamma, y, y') = gamma^{\min\{k\in \mathbb{N} \mid q(\operatorname{iterate}(tau, k, y)) \neq q(\operatorname{iterate}(tau, k, y'))\}})}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/ItineraryFirstDifferencePowerLaw.itinerary_first_difference_power_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Future indistinguishability is the canonical equality of complete readout itineraries. The distance is the existing discounted supremum using the discrete output discrepancy.

Equal complete itineraries make every discrepancy term zero. If the states are distinguishable, the least separating time gives the largest nonzero discounted term.

Both source clauses remain public: zero distance for canonically future-indistinguishable states and the exact first-difference power law for distinguishable states.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/ItineraryFirstDifferencePowerLaw.itinerary_first_difference_power_law`
- Dependency: [D5/S3/Observer/MetricGeometry/BellmanMaxEquation](../MetricGeometry/BellmanMaxEquation.md)
- Dependency: [D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric](../MetricGeometry/DiscretePredictionUltrametric.md)
- Dependency: [D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap](../../ObserverMemory/InverseLimits/IdentityFuturePastGap.md)
