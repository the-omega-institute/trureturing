# Strict-past endpoint hazard and recurrence

## Abstract

Actual endpoint-cycle hits have a strict-past hazard, whose almost-sure divergence forces recurrent hits.

Fix an integer initial offset e and write A(k,e) for the event that actual marked cycle k hits at the offset obtained by adding the first k discrepancy advances to e. The strict past at k contains exactly those k completed marks. For each strict-past measurable set S, M(S,k,e) is the stream mass of S intersected with A(k,e), and I(S,k,e) is the nonnegative integral on S of the next-cycle hazard at that incoming offset.

**Theorem 1.1 (Conditional probability identity and arbitrarily late shifted hits).**

$$(\forall k,S, \operatorname{Past}\left(S, k\right)\Rightarrow\operatorname{M}\left(S, k, e\right) = \operatorname{I}\left(S, k, e\right)) \land (\operatorname{D}\left(e\right)\Rightarrow\operatorname{R}\left(e\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointPredictableHazard.actual_predictable_hazard_and_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here D(e) denotes almost-sure divergence of the sum of actual next-cycle hazards. R(e) means that almost surely, for every natural-number threshold N there is a cycle k at or after N in A(k,e). The testing identity is unconditional; only the recurrence implication uses D(e).

An exact prefix box fixes the incoming offset and factors from the next marked coordinate. The disjoint countable partition of a past event into such boxes gives the test identity. The hazard is bounded by one and is measurable in the strict past, so the nonnegative integral identity identifies its real value with the real conditional expectation of the next hit indicator.

The hit at k is measurable after revealing mark k, namely at filtration stage k+1. With an empty stage-zero event, Lévy's generalized Borel–Cantelli theorem therefore uses the hazard at stage k, not the filtration that already contains the upcoming mark. The conclusion assumes no independence of hit events and does not assert a finite-permutation limit or unconditional divergence.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointPredictableHazard.actual_predictable_hazard_and_recurrence`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit](EndpointFirstCycleHitLimit.md)
