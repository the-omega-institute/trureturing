# Primitive Golden Period-Twelve Certificates

## Abstract

Twenty-five exact primitive period-twelve orbit certificates extend the golden table.

The period-twelve branch words and quadratic coordinates are stated exactly over Q(phi).

**Theorem 1.1 (Twenty-five primitive period-twelve orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesExactlyTwelve}\right) = 25$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData.golden_new_periodic_orbit_count_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each representative carries a twelve-step closed itinerary.

**Theorem 1.2 (The period-twelve representatives are valid).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyTwelve},\; \operatorname{goldenCodedOrbitValid}\left(O\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData.golden_new_periodic_orbit_representatives_valid_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every displayed code follows its source, target, and affine branch rules and closes after twelve steps.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData.golden_new_periodic_orbit_count_twelve`
- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData.golden_new_periodic_orbit_representatives_valid_twelve`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationEleven](../GoldenPeriodic/EnumerationEleven.md)
