# Tribonacci Period-Eight Orbit Data

## Abstract

Fifteen exact primitive cycles supply the new Tribonacci period-eight data.

**Theorem 1.1 (Fifteen new primitive period-eight orbits).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesExactlyEight}\right) = 15$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData.tribonacci_new_periodic_orbit_count_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotation reduction of the one hundred twenty new phase states gives fifteen representatives, each with eight transitions.

**Theorem 1.2 (All fifteen new period-eight orbits are valid).**

$$\operatorname{Forall}\left(\mathit{tribonacciPeriodicOrbitRepresentativesExactlyEight}, \mathit{tribonacciCodedOrbitValid}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData.tribonacci_new_periodic_orbit_representatives_valid_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eight bounded exact proof groups certify branch choices, gap bounds, closure, and phase distinctness under the default limits.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData.tribonacci_new_periodic_orbit_count_eight`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData.tribonacci_new_periodic_orbit_representatives_valid_eight`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSeven](../TribonacciPeriodic/EnumerationSeven.md)
