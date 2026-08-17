# Golden Periodic Enumeration Through Eleven

## Abstract

The exact golden periodic enumeration is complete through period eleven.

The period-ten certificate and eighteen primitive eleven-cycles are combined through a 199-equation exact fixed-point census.

**Theorem 1.1 (Four hundred eighty periodic points through eleven).**

$$\operatorname{card}\left(\mathit{goldenPeriodicPointCodesEleven}\right) = 480$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_point_code_count_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eighteen primitive eleven-cycles add 198 phases to the 282 phases enumerated through period ten.

**Theorem 1.2 (Fifty-four disjoint periodic orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesEleven}\right) = 54 \land \operatorname{card}\left(\mathit{goldenEnumeratedOrbitStatesEleven}\right) = 480$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_code_partition_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 36 prior cycles and eighteen primitive eleven-cycles have no repeated exact phase code.

**Theorem 1.3 (The enumeration through period eleven is complete).**

$$\forall p \in N, s \in \mathit{GoldenSurvivorState},\; \left(\left(p \ge 1 \land p \le 11\right) \land \operatorname{iterate}\left(\mathit{goldenTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionEleven}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_orbit_enumeration_complete_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real state fixed by a nonzero iterate of period at most eleven lies on one of the fifty-four decoded exact cycles.

**Theorem 1.4 (The golden periodic maximin through eleven).**

$$\operatorname{IsGreatest}\left(\mathit{goldenPeriodicOrbitMinimaEleven}, \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_orbit_maximin_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every new low-arm witness is bounded by the threshold, and the period-three champion continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_code_partition_eleven`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_orbit_enumeration_complete_eleven`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_orbit_maximin_eleven`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEleven.golden_periodic_point_code_count_eleven`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed](EnumerationElevenFixed.md)
