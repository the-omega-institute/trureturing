# Primitive Golden Period-Eleven Certificates

## Abstract

Eighteen exact primitive period-eleven orbit certificates extend the golden table.

The period-eleven branch words and quadratic coordinates are stated exactly over Q(phi).

**Theorem 1.1 (Eighteen primitive period-eleven orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesExactlyEleven}\right) = 18$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenData.golden_new_periodic_orbit_count_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each representative carries an eleven-step closed itinerary.

**Theorem 1.2 (The period-eleven representatives are valid).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyEleven},\; \operatorname{goldenCodedOrbitValid}\left(O\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenData.golden_new_periodic_orbit_representatives_valid_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every displayed code follows its source, target, and affine branch rules and closes after eleven steps.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenData.golden_new_periodic_orbit_count_eleven`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenData.golden_new_periodic_orbit_representatives_valid_eleven`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationTen](EnumerationTen.md)
