# Tribonacci Period-Six Separation

## Abstract

The old and new Tribonacci phase codes form one duplicate-free period-six list.

**Theorem 1.1 (Old and new phase codes are disjoint).**

$$\operatorname{Disjoint}\left(\mathit{tribonacciEnumeratedOrbitStatesFiveList}, \mathit{tribonacciEnumeratedOrbitStatesExactlySixList}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint.tribonacci_old_new_periodic_orbit_state_codes_disjoint_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three bounded exact comparisons separate each new orbit from the thirty-seven previously certified phase states.

**Theorem 1.2 (All period-six phase codes are distinct).**

$$\operatorname{Nodup}\left(\mathit{tribonacciEnumeratedOrbitStatesSixList}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint.tribonacci_periodic_orbit_state_codes_nodup_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prior distinctness, new distinctness, and old-new separation combine without re-expanding a monolithic comparison.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint.tribonacci_old_new_periodic_orbit_state_codes_disjoint_six`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint.tribonacci_periodic_orbit_state_codes_nodup_six`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSixData](EnumerationSixData.md)
