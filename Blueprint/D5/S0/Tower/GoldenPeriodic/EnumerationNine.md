# Golden Periodic Enumeration Through Nine

## Abstract

The exact golden periodic enumeration is complete through period nine.

The period-eight theorem and eight new primitive period-nine cycles are combined without expanding one monolithic arithmetic proof. A first- and second-step partition keeps the finite comparisons bounded.

**Theorem 1.1 (One hundred seventy-two periodic points through period nine).**

$$\operatorname{card}\left(\mathit{goldenPeriodicPointCodesNine}\right) = 172$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_point_code_count_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eight primitive nine-cycles contribute seventy-two new phase states to the one hundred states known through period eight.

**Theorem 1.2 (Twenty-five disjoint periodic orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesNine}\right) = 25 \land \operatorname{card}\left(\mathit{goldenEnumeratedOrbitStatesNine}\right) = 172$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_code_partition_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact state table splits without repetition into seventeen prior cycles and eight primitive cycles of length nine.

**Theorem 1.3 (The enumeration through period nine is complete).**

$$\forall p \in N, s \in \mathit{GoldenSurvivorState},\; \left(\left(p \ge 1 \land p \le 9\right) \land \operatorname{iterate}\left(\mathit{goldenTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionNine}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_orbit_enumeration_complete_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real state fixed by a nonzero iterate of period at most nine occurs on one of the twenty-five decoded exact cycles.

**Theorem 1.4 (The golden periodic maximin through nine).**

$$\operatorname{IsGreatest}\left(\mathit{goldenPeriodicOrbitMinimaNine}, \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_orbit_maximin_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All new cycles stay below the exact threshold, while the inherited period-three champion continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_code_partition_nine`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_orbit_enumeration_complete_nine`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_orbit_maximin_nine`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNine.golden_periodic_point_code_count_nine`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationNineData](EnumerationNineData.md)
