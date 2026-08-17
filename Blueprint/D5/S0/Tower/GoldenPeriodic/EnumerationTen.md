# Golden Periodic Enumeration Through Ten

## Abstract

The exact golden periodic enumeration is complete through period ten.

The period-nine theorem and eleven new primitive period-ten cycles are combined through an eight-block fixed-point decomposition.

**Theorem 1.1 (Two hundred eighty-two periodic points through period ten).**

$$\operatorname{card}\left(\mathit{goldenPeriodicPointCodesTen}\right) = 282$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_point_code_count_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eleven primitive ten-cycles contribute one hundred ten new phase states to the 172 states known through period nine.

**Theorem 1.2 (Thirty-six disjoint periodic orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesTen}\right) = 36 \land \operatorname{card}\left(\mathit{goldenEnumeratedOrbitStatesTen}\right) = 282$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_code_partition_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact state table splits without repetition into twenty-five prior cycles and eleven primitive cycles of length ten.

**Theorem 1.3 (The enumeration through period ten is complete).**

$$\forall p \in N, s \in \mathit{GoldenSurvivorState},\; \left(\left(p \ge 1 \land p \le 10\right) \land \operatorname{iterate}\left(\mathit{goldenTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnionTen}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_orbit_enumeration_complete_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real state fixed by a nonzero iterate of period at most ten occurs on one of the thirty-six decoded exact cycles.

**Theorem 1.4 (The golden periodic maximin through ten).**

$$\operatorname{IsGreatest}\left(\mathit{goldenPeriodicOrbitMinimaTen}, \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_orbit_maximin_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All new cycles stay below the exact threshold, while the inherited period-three champion continues to attain equality.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_code_partition_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_orbit_enumeration_complete_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_orbit_maximin_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTen.golden_periodic_point_code_count_ten`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed](EnumerationTenFixed.md)
