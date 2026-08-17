# Primitive Golden Period-Nine Certificates

## Abstract

Eight exact primitive period-nine orbit certificates extend the golden data table.

The period-nine branch words are solved exactly over Q(phi). Their closure, validity, separation from earlier periods, and low-arm witnesses are checked in bounded groups.

**Theorem 1.1 (Eight primitive period-nine orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesExactlyNine}\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_count_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact table contains eight representatives, each carrying a nine-step closed itinerary.

**Theorem 1.2 (The period-nine representatives are valid).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyNine},\; \operatorname{goldenCodedOrbitValid}\left(O\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_representatives_valid_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every displayed code remains in the unit interval and follows the source, target, and affine rules of its branch word.

**Theorem 1.3 (The seventy-two new state codes are distinct).**

$$\operatorname{Nodup}\left(\operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesExactlyNine}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_state_codes_nodup_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening the eight nine-cycles produces no repeated exact state code.

**Theorem 1.4 (Period-nine low arms obey the golden bound).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyNine},\; \operatorname{goldenStateArm}\left(\operatorname{decodeGoldenState}\left(\operatorname{lowState}\left(O\right)\right)\right) \le \mathit{goldenThreshold}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_low_arms_bounded_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each new cycle has an explicit member whose arm is at most the exact golden threshold.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_count_nine`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_low_arms_bounded_nine`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_representatives_valid_nine`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationNineData.golden_new_periodic_orbit_state_codes_nodup_nine`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationEight](EnumerationEight.md)
