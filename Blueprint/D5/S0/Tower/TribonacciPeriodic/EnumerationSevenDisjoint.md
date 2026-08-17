# Tribonacci Period-Seven Separation

## Abstract

The old and new Tribonacci phase codes form one duplicate-free period-seven list.

**Theorem 1.1 (Old and new period-seven phase codes are disjoint).**

$$\operatorname{Disjoint}\left(\mathit{tribonacciPhaseStatesThroughSix}, \mathit{tribonacciPhaseStatesExactlySeven}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint.tribonacci_old_new_periodic_orbit_state_codes_disjoint_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ten isolated comparisons combine the two historical levels without re-expanding one monolithic sixty-seven-by-seventy check.

**Theorem 1.2 (All phase codes through seven are distinct).**

$$\operatorname{Nodup}\left(\mathit{tribonacciPhaseStatesThroughSeven}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint.tribonacci_periodic_orbit_state_codes_nodup_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prior sixty-seven phases and seventy new phases combine into a duplicate-free cumulative list.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint.tribonacci_old_new_periodic_orbit_state_codes_disjoint_seven`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint.tribonacci_periodic_orbit_state_codes_nodup_seven`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDistinct](EnumerationSevenDistinct.md)
