# Tribonacci Periodic Enumeration

## Abstract

Exact computation supplies ten valid, disjoint Tribonacci cycles through period five.

**Theorem 1.1 (Fixed-point equation counts through period five).**

$$\operatorname{fixedPointEquationCountsThrough}\left(5\right) = \operatorname{list}\left(1, 3, 7, 11, 21\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_fixed_point_counts_through_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed-walk generator produces 1, 3, 7, 11, and 21 phase-marked fixed-point equations at periods one through five.

**Theorem 1.2 (The ten orbit periods are explicit).**

$$\operatorname{orbitPeriodList}\left(\mathit{tribonacciPeriodicOrbitRepresentativesFive}\right) = \operatorname{list}\left(1, 2, 3, 3, 4, 4, 5, 5, 5, 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_period_distribution_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one primitive cycle of periods one and two, two cycles of periods three and four, and four cycles of period five.

**Theorem 1.3 (Every representative uses valid branches).**

$$\operatorname{Forall}\left(\mathit{tribonacciPeriodicOrbitRepresentativesFive}, \mathit{tribonacciCodedOrbitValid}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_representatives_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact cubic inequalities certify the source gap, branch side, target gap, and closure condition for every displayed representative.

**Theorem 1.4 (Coded phase states are globally disjoint).**

$$\operatorname{Nodup}\left(\operatorname{flatMapOrbitStates}\left(\mathit{tribonacciPeriodicOrbitRepresentativesFive}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_state_codes_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening all ten cycles gives a list with no repeated exact cubic state code, including across different representatives.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_fixed_point_counts_through_five`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_period_distribution_five`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_representatives_valid`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_state_codes_nodup`
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](ChampionValue.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator](TribonacciPeriodicGenerator.md)
