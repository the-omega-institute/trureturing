# Golden Permanent Survivors

## Abstract

Strict golden survival has no permanent state; the closed threshold has a larger proved preperiodic carrier.

The source conflated two different constructions. Intersecting the closures of the four strict finite-depth tubes gives four limiting points, but permanent survival for the closed threshold also retains boundary preimages. The strict threshold is the usable replacement for the upper-bound argument.

**Theorem 1.1 (The strict permanent survivor set is empty).**

$$\mathit{goldenStrictPermanentSet} = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenPermanentSurvivors.golden_strict_permanent_set_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise classification places any hypothetical strict permanent state in the four-point closed-tube limit. Each of those four points is an excluded endpoint of the open depth-two tubes, so no state survives every strict backward depth.

**Theorem 1.2 (The known closed preperiodic carrier survives).**

$$\forall s \in \mathit{GoldenSurvivorState},\; \operatorname{IsGoldenKnownClosedPreperiodicState}\left(s\right) \Rightarrow \left(\forall n \in N,\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenClosedSurvivorSet}, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenPermanentSurvivors.golden_known_closed_preperiodic_carrier_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved carrier has eight states: the large-gap threshold point plus the frozen seven-state carrier. The threshold point maps directly to the tail. The counterexample used by the frozen theorem is the large-gap state with coordinate (9 minus 5 phi) over 2; its orbit passes through the large coordinate (4 phi minus 5) over 2, the small and large tail coordinates phi inverse over 2, and then the three-state champion cycle. The inclusion is deliberately not stated as equality and does not claim a complete closed-set classification.

## References

- Truth anchor: `D5/S0/Tower/Champions/GoldenPermanentSurvivors.golden_known_closed_preperiodic_carrier_subset`
- Truth anchor: `D5/S0/Tower/Champions/GoldenPermanentSurvivors.golden_strict_permanent_set_eq_empty`
- Dependency: [D5/S0/Tower/Champions/GoldenSurvivorClassification](GoldenSurvivorClassification.md)
