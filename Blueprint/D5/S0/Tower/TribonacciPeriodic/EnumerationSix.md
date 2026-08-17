# Tribonacci Periodic Enumeration Through Six

## Abstract

The complete Tribonacci periodic enumeration through six has unchanged champion maximin.

**Theorem 1.1 (Fifteen cycles and sixty-seven phase states).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesSix}\right) = 15 \land \operatorname{card}\left(\mathit{tribonacciEnumeratedOrbitStatesSix}\right) = 67$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSix.tribonacci_periodic_code_partition_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Five primitive six-cycles add thirty phases to the prior ten cycles and thirty-seven phases.

**Theorem 1.2 (The enumeration through six is complete).**

$$\forall p \in N, s \in \mathit{TribonacciPeriodicState},\; \left(\left(p \ge 1 \land p \le 6\right) \land \operatorname{iterate}\left(\mathit{tribonacciPeriodicTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionSix}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSix.tribonacci_periodic_orbit_enumeration_complete_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real branch state fixed by a nonzero iterate of period at most six occurs on one of the fifteen decoded cycles.

**Theorem 1.3 (The periodic maximin through six is unchanged).**

$$\operatorname{IsGreatest}\left(\mathit{tribonacciPeriodicOrbitMinimaSix}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodic/EnumerationSix.tribonacci_periodic_orbit_maximin_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each new cycle has a certified low arm below championValue(t), while the repeating ba orbit continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSix.tribonacci_periodic_code_partition_six`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSix.tribonacci_periodic_orbit_enumeration_complete_six`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodic/EnumerationSix.tribonacci_periodic_orbit_maximin_six`
- Dependency: [D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed](EnumerationSixFixed.md)
