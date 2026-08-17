# Tribonacci Periodic Enumeration Through Eight

## Abstract

The complete Tribonacci periodic enumeration through eight has unchanged champion maximin.

**Theorem 1.1 (Forty cycles and two hundred fifty-seven phase certificates).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesEight}\right) = 40 \land \operatorname{length}\left(\mathit{tribonacciPeriodicOrbitPhaseCertificatesEight}\right) = 257$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight.tribonacci_periodic_code_partition_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fifteen primitive eight-cycles add one hundred twenty phases to the prior twenty-five cycles and one hundred thirty-seven phases.

**Theorem 1.2 (The enumeration through eight is complete).**

$$\forall p \in N, s \in \mathit{TribonacciPeriodicState},\; \left(\left(p \ge 1 \land p \le 8\right) \land \operatorname{iterate}\left(\mathit{tribonacciPeriodicTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionEight}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight.tribonacci_periodic_orbit_enumeration_complete_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real branch state fixed by a nonzero iterate of period at most eight occurs on one of the forty decoded cycles.

**Theorem 1.3 (The periodic maximin through eight is unchanged).**

$$\operatorname{IsGreatest}\left(\mathit{tribonacciPeriodicOrbitMinimaEight}, \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight.tribonacci_periodic_orbit_maximin_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each new cycle has a certified low arm below championValue(t), while the repeating ba orbit continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight.tribonacci_periodic_code_partition_eight`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight.tribonacci_periodic_orbit_enumeration_complete_eight`
- Truth anchor: `D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight.tribonacci_periodic_orbit_maximin_eight`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightMaximinA](EnumerationEightMaximinA.md)
