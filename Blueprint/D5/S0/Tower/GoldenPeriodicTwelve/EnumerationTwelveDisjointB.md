# Period-Twelve Separation From Earlier Periods

## Abstract

All primitive period-twelve states are separated from every earlier state.

The twelve remaining cycles are checked and combined with the first thirteen separation certificates.

**Theorem 1.1 (New states are disjoint from all earlier states).**

$$\operatorname{Disjoint}\left(\operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesEleven}\right), \operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesExactlyTwelve}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB.golden_old_new_periodic_orbit_state_codes_disjoint_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No exact phase code on a primitive twelve-cycle occurs on an orbit enumerated through period eleven.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB.golden_old_new_periodic_orbit_state_codes_disjoint_twelve`
- Dependency: [D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointA](EnumerationTwelveDisjointA.md)
