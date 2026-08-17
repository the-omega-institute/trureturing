# Distinct Period-Twelve State Codes

## Abstract

The 300 new period-twelve state codes are pairwise distinct.

Seven bounded orbit groups are checked internally and pairwise before their state lists are recombined.

**Theorem 1.1 (The 300 new state codes are distinct).**

$$\operatorname{Nodup}\left(\operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesExactlyTwelve}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDistinct.golden_new_periodic_orbit_state_codes_nodup_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening the twenty-five exact twelve-cycles introduces no repeated quadratic state code.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDistinct.golden_new_periodic_orbit_state_codes_nodup_twelve`
- Dependency: [D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData](EnumerationTwelveData.md)
