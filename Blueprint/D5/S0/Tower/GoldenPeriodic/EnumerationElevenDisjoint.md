# Period-Eleven Separation From Earlier Periods

## Abstract

The primitive period-eleven states do not collide with any state through ten.

Each new orbit is checked against the frozen period-nine states and the period-ten extension, then the results are recombined.

**Theorem 1.1 (New states are disjoint from all earlier states).**

$$\operatorname{Disjoint}\left(\operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesTen}\right), \operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesExactlyEleven}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint.golden_old_new_periodic_orbit_state_codes_disjoint_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No exact phase code on a primitive eleven-cycle occurs on an orbit enumerated through period ten.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint.golden_old_new_periodic_orbit_state_codes_disjoint_eleven`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct](EnumerationElevenDistinct.md)
