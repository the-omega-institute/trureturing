# Golden Periodic Enumeration Through Twelve

## Abstract

The exact golden periodic enumeration is complete through period twelve.

The period-eleven certificate and twenty-five primitive twelve-cycles are combined through a 322-equation exact fixed-point census.

**Theorem 1.1 (Seven hundred eighty periodic points through twelve).**

$$\operatorname{card}\left(\mathit{goldenPeriodicPointCodesTwelve}\right) = 780$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_point_code_count_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twenty-five primitive twelve-cycles add 300 phases to the 480 phases enumerated through period eleven.

**Theorem 1.2 (Seventy-nine disjoint periodic orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesTwelve}\right) = 79 \land \operatorname{card}\left(\mathit{goldenEnumeratedOrbitStatesTwelve}\right) = 780$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_code_partition_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 54 prior cycles and twenty-five primitive twelve-cycles have no repeated exact phase code.

**Theorem 1.3 (The enumeration through period twelve is complete).**

$$\forall p \in N, s \in \mathit{GoldenSurvivorState},\; \left(\left(p \ge 1 \land p \le 12\right) \land \operatorname{iterate}\left(\mathit{goldenTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionTwelve}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_orbit_enumeration_complete_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real state fixed by a nonzero iterate of period at most twelve lies on one of the 79 decoded exact cycles.

**Theorem 1.4 (The golden periodic maximin through twelve).**

$$\operatorname{IsGreatest}\left(\mathit{goldenPeriodicOrbitMinimaTwelve}, \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_orbit_maximin_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every new low-arm witness is bounded by the threshold, and the period-three champion continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_code_partition_twelve`
- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_orbit_enumeration_complete_twelve`
- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_orbit_maximin_twelve`
- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve.golden_periodic_point_code_count_twelve`
- Dependency: [D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed](EnumerationTwelveFixed.md)
