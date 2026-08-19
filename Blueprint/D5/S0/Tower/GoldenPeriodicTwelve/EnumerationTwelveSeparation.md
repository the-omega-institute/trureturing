# Period-Twelve Five-Step Separation

## Abstract

The period-twelve phases admit a five-step partition and low-arm witnesses.

Twenty-one legal five-step prefixes partition every inherited and new phase fixed by the twelfth iterate.

**Theorem 1.1 (Period-twelve low arms obey the golden bound).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyTwelve},\; \operatorname{goldenStateArm}\left(\operatorname{decodeGoldenState}\left(\operatorname{lowState}\left(O\right)\right)\right) \le \mathit{goldenThreshold}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation.golden_new_periodic_orbit_low_arms_bounded_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each primitive twelve-cycle has an explicit phase whose arm is at most the exact golden threshold.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation.golden_new_periodic_orbit_low_arms_bounded_twelve`
- Dependency: [D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB](EnumerationTwelveDisjointB.md)
