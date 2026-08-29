# Toroidal Cech Completion

## Abstract

Quadratic-period ratios agree on overlaps and glue uniquely to the completed-zeta amplitude.

**Theorem 1.1 (Quadratic-period charts glue uniquely to xi).**

$$\forall Index \in \operatorname{Type}\left(\right), Omega \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right), P \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\left(\forall i \in Index,\; \operatorname{Continuous}\left(P\left(i\right)\right)\right) \land \left(\left(\forall i \in Index,\; \operatorname{Continuous}\left(T\left(i\right)\right)\right) \land \left(\left(\forall i \in Index, s \in \operatorname{Complex}\left(\right),\; P\left(i\right)\left(s\right) = xiReading\left(s\right) \times T\left(i\right)\left(s\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, Omega\right) \Rightarrow \left(\exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in Index, j \in Index, s \in \operatorname{Subtype}\left(Omega\right),\; \left(\operatorname{mem}\left(s, \operatorname{nonvanishingDomain}\left(Omega, T, i\right)\right) \land \operatorname{mem}\left(s, \operatorname{nonvanishingDomain}\left(Omega, T, j\right)\right)\right) \Rightarrow \operatorname{localPeriodRatio}\left(Omega, P, T, i, s\right) = \operatorname{localPeriodRatio}\left(Omega, P, T, j, s\right)\right) \land \left(\left(\forall i \in Index, s \in \operatorname{Subtype}\left(Omega\right),\; \operatorname{mem}\left(s, \operatorname{nonvanishingDomain}\left(Omega, T, i\right)\right) \Rightarrow xiReading\left(s\right) = \operatorname{localPeriodRatio}\left(Omega, P, T, i, s\right)\right) \land \left(\forall g \in \operatorname{ContinuousMap}\left(\operatorname{Subtype}\left(Omega\right), \operatorname{Complex}\left(\right)\right),\; \left(\forall i \in Index, s \in \operatorname{Subtype}\left(Omega\right),\; \operatorname{mem}\left(s, \operatorname{nonvanishingDomain}\left(Omega, T, i\right)\right) \Rightarrow g\left(s\right) = \operatorname{localPeriodRatio}\left(Omega, P, T, i, s\right)\right) \Rightarrow g = \operatorname{restrictedXi}\left(Omega\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalCechCompletion.toroidal_cech_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each chart is constructed as the nonvanishing domain of one twist. Continuity of the period and twist constructs the local period-over-twist map on that exact subtype.

The displayed factorization identifies every local ratio with the repository's canonical entire xi reading. The pointwise nonvanishing hypothesis says these charts cover Omega.

The frozen continuous local-factor gluing theorem supplies overlap compatibility and the unique continuous glue. Its computation rule identifies that glue with restrictedXi on every chart.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalCechCompletion.toroidal_cech_completion`
- Dependency: [D5/S3/ConceptDynamics/Gluing/ContinuousLocalFactorGluing](../../ConceptDynamics/Gluing/ContinuousLocalFactorGluing.md)
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
