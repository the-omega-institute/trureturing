# Distinct Period-Eleven State Codes

## Abstract

The 198 new period-eleven state codes are pairwise distinct.

Four bounded orbit groups are checked internally and pairwise before their state lists are recombined.

**Theorem 1.1 (The 198 new state codes are distinct).**

$$\operatorname{Nodup}\left(\operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesExactlyEleven}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct.golden_new_periodic_orbit_state_codes_nodup_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening the eighteen exact eleven-cycles introduces no repeated quadratic state code.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct.golden_new_periodic_orbit_state_codes_nodup_eleven`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationElevenData](EnumerationElevenData.md)
