# Golden Periodic Enumeration Through Eight

## Abstract

One incremental exact certificate extends the golden periodic enumeration through period eight.

The frozen period-at-most-seven certificate is reused without expansion. Only period-eight branch words are solved over Q(phi), then split by their first transition so each finite check remains bounded.

**Theorem 1.1 (One hundred periodic points through period eight).**

$$\operatorname{card}\left(\mathit{goldenPeriodicPointCodesEight}\right) = 100$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_point_code_count_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five new primitive period-eight cycles contribute forty new phase states; together with the frozen sixty states this gives one hundred.

**Theorem 1.2 (Seventeen disjoint periodic orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesEight}\right) = 17 \land \operatorname{card}\left(\mathit{goldenEnumeratedOrbitStatesEight}\right) = 100$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_code_partition_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one hundred exact state codes split without repetition into the twelve frozen cycles and five primitive cycles of length eight.

**Theorem 1.3 (The enumeration through period eight is complete).**

$$\forall p \in N, s \in \mathit{GoldenSurvivorState},\; \left(\left(p \ge 1 \land p \le 8\right) \land \operatorname{iterate}\left(\mathit{goldenTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionEight}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_orbit_enumeration_complete_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real state fixed by a nonzero iterate of period at most eight occurs on one of the seventeen decoded exact cycles.

**Theorem 1.4 (The golden periodic maximin through eight).**

$$\operatorname{IsGreatest}\left(\mathit{goldenPeriodicOrbitMinimaEight}, \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_orbit_maximin_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each new cycle has a certified low state whose arm is at most phi inverse squared over two, while the frozen period-three cycle continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_code_partition_eight`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_orbit_enumeration_complete_eight`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_orbit_maximin_eight`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationEight.golden_periodic_point_code_count_eight`
- Dependency: [D5/S0/Tower/Champions/GoldenPeriodicEnumeration](../Champions/GoldenPeriodicEnumeration.md)
