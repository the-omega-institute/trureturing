# Tribonacci Periodic Enumeration Through Seven

## Abstract

The complete Tribonacci periodic enumeration through seven has unchanged champion maximin.

**Theorem 1.1 (Twenty-five cycles and one hundred thirty-seven phase states).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesSeven}\right) = 25 \land \operatorname{card}\left(\mathit{tribonacciEnumeratedOrbitStatesSeven}\right) = 137$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSeven.tribonacci_periodic_code_partition_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ten primitive seven-cycles add seventy phases to the prior fifteen cycles and sixty-seven phases.

**Theorem 1.2 (The enumeration through seven is complete).**

$$\forall p \in N, s \in \mathit{TribonacciPeriodicState},\; \left(\left(p \ge 1 \land p \le 7\right) \land \operatorname{iterate}\left(\mathit{tribonacciPeriodicTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionSeven}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSeven.tribonacci_periodic_orbit_enumeration_complete_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real branch state fixed by a nonzero iterate of period at most seven occurs on one of the twenty-five decoded cycles.

**Theorem 1.3 (The periodic maximin through seven is unchanged).**

$$\operatorname{IsGreatest}\left(\mathit{tribonacciPeriodicOrbitMinimaSeven}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSeven.tribonacci_periodic_orbit_maximin_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each new cycle has a certified low arm below championValue(t), while the repeating ba orbit continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSeven.tribonacci_periodic_code_partition_seven`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSeven.tribonacci_periodic_orbit_enumeration_complete_seven`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSeven.tribonacci_periodic_orbit_maximin_seven`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSevenMaximinA](EnumerationSevenMaximinA.md)
