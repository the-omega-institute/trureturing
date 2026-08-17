# Period-Eleven Prefix Separation

## Abstract

The period-eleven phases admit bounded prefix partitions and low-arm witnesses.

Three-step prefixes partition every expected phase; the three 34-state blocks are refined once more by their fourth step.

**Theorem 1.1 (Period-eleven low arms obey the golden bound).**

$$\forall O \in \mathit{goldenPeriodicOrbitRepresentativesExactlyEleven},\; \operatorname{goldenStateArm}\left(\operatorname{decodeGoldenState}\left(\operatorname{lowState}\left(O\right)\right)\right) \le \mathit{goldenThreshold}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation.golden_new_periodic_orbit_low_arms_bounded_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each primitive eleven-cycle has an explicit phase whose arm is at most the exact golden threshold.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation.golden_new_periodic_orbit_low_arms_bounded_eleven`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint](EnumerationElevenDisjoint.md)
