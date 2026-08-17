# Tribonacci Period-Seven Orbit Data

## Abstract

Ten exact primitive cycles supply the new Tribonacci period-seven data.

**Theorem 1.1 (Ten new primitive period-seven orbits).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesExactlySeven}\right) = 10$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData.tribonacci_new_periodic_orbit_count_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotation reduction of the seventy new phase states gives ten representatives, each with seven transitions.

**Theorem 1.2 (All ten new period-seven orbits are valid).**

$$\operatorname{Forall}\left(\mathit{tribonacciPeriodicOrbitRepresentativesExactlySeven}, \mathit{tribonacciCodedOrbitValid}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData.tribonacci_new_periodic_orbit_representatives_valid_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Five bounded exact proof groups certify branch choices, gap bounds, and closure under the default resource limits.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData.tribonacci_new_periodic_orbit_count_seven`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData.tribonacci_new_periodic_orbit_representatives_valid_seven`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSix](EnumerationSix.md)
