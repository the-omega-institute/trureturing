# Tribonacci Period-Six Orbit Data

## Abstract

Five exact primitive cycles supply the new Tribonacci period-six data.

**Theorem 1.1 (Five new primitive period-six orbits).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesExactlySix}\right) = 5$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSixData.tribonacci_new_periodic_orbit_count_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotation reduction of the thirty new phase states gives five representatives, each with six transitions.

**Theorem 1.2 (All five new orbits are valid).**

$$\operatorname{Forall}\left(\mathit{tribonacciPeriodicOrbitRepresentativesExactlySix}, \mathit{tribonacciCodedOrbitValid}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSixData.tribonacci_new_periodic_orbit_representatives_valid_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact cubic inequalities certify every branch choice, gap bound, and closing equation without numerical approximation.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSixData.tribonacci_new_periodic_orbit_count_six`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSixData.tribonacci_new_periodic_orbit_representatives_valid_six`
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin](../DBonacciGeneral/TribonacciPeriodicMaximin.md)
