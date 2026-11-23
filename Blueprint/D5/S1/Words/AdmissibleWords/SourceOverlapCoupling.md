# Realizing prescribed overlaps with a source event

## Abstract

Splitting the unit interval at a source mass realizes compatible overlaps.

**Theorem 1.1 (Nested events with prescribed source overlaps).**

Lean statement: `D5/S1/Words/AdmissibleWords/SourceOverlapCoupling.exists_nested_events`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/SourceOverlapCoupling.exists_nested_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A marginal and its proposed overlap with a fixed source prescribe two masses, one inside the source and one outside. Each must fit inside its part of the unit interval. Both masses must be nondecreasing across each required inclusion, and the source must have full overlap with itself. Take the initial interval of the prescribed length in each part. Their union is Lebesgue measurable and realizes the marginal, the source overlap and every required inclusion.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/SourceOverlapCoupling.exists_nested_events`
