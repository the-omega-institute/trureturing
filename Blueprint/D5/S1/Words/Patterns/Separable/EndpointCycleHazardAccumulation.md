# Hazard accumulation and recurrence for the actual cycle stream

## Abstract

The actual hazards diverge and actual shifted hits recur on one event of full measure for each initial offset.

**Theorem 1.1 (Infinite total hazard and arbitrarily late shifted hits).**

$$\forall e\in \mathbb{Z},\quad\operatorname{streamMeasure}\left(\{w\in Stream\mid \sum_{j\in \mathbb{N}} \operatorname{nextHazard}\left(e+\operatorname{streamDiscrepancy}\left(j, w\right)\right)= \infty \land (\forall N\in \mathbb{N}, \exists k\in \mathbb{N}, N\le k \land w\in \operatorname{hitAt}\left(e, k\right))\}^{c}\right)= 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointCycleHazardAccumulation.actual_hazard_accumulation_and_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer e is the initial discrepancy. The stream sample w is distributed by the actual mark law. At index j, the incoming discrepancy is e plus the discrepancy of the j completed marks. The event hitAt(e,k) tests the actual mark k at this incoming discrepancy, before adding its own advance.

The uniform quadratic marginal bound gives divergence of the sum of the logarithmic discrepancy profile. The raw occupation lower envelope bounds the first term of the exact nonnegative hazard series. A positive multiple of the divergent profile sum is therefore no greater than the total actual hazard. The strict-past conditional recurrence theorem then gives hits beyond every threshold on the same full-measure event, without any independence assumption on the hit events.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointCycleHazardAccumulation.actual_hazard_accumulation_and_recurrence`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries](../../../../S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.md)
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries](EndpointCycleHazardSeries.md)
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointPredictableHazard](EndpointPredictableHazard.md)
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointQuadraticMarginal](EndpointQuadraticMarginal.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedLogEnvelope](OccupiedLogEnvelope.md)
