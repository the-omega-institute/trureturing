# Primitive Golden Period-Ten Certificates

## Abstract

Eleven exact primitive period-ten orbit certificates extend the golden data table.

The period-ten branch words are solved exactly over Q(phi). Their closure, validity, separation from earlier periods, and low-arm witnesses are checked in bounded pairs and a final singleton.

**Theorem 1.1 (Eleven primitive period-ten orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesExactlyTen}\right) = 11$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_count_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact table contains eleven representatives, each carrying a ten-step closed itinerary.

**Theorem 1.2 (The period-ten representatives are valid).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyTen},\; \operatorname{goldenCodedOrbitValid}\left(O\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_representatives_valid_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every displayed code remains in the unit interval and follows the source, target, and affine rules of its branch word.

**Theorem 1.3 (The one hundred ten new state codes are distinct).**

$$\operatorname{Nodup}\left(\operatorname{flatMap}\left(\mathit{goldenOrbitStates}, \mathit{goldenPeriodicOrbitRepresentativesExactlyTen}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_state_codes_nodup_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening the eleven ten-cycles produces no repeated exact state code and no collision with the earlier enumeration.

**Theorem 1.4 (Period-ten low arms obey the golden bound).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyTen},\; \operatorname{goldenStateArm}\left(\operatorname{decodeGoldenState}\left(\operatorname{lowState}\left(O\right)\right)\right) \le \mathit{goldenThreshold}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_low_arms_bounded_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each new cycle has an explicit member whose arm is at most the exact golden threshold.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_count_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_low_arms_bounded_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_representatives_valid_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTenData.golden_new_periodic_orbit_state_codes_nodup_ten`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationNine](EnumerationNine.md)
