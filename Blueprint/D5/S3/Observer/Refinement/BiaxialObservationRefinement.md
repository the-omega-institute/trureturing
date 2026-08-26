# Biaxial Observation Refinement

## Abstract

Joint refinement enlarges the observation schedule and shrinks its indistinguishability relation.

**Theorem 1.1 (Both observation axes refine in their natural directions).**

$$\begin{aligned}\forall X: \operatorname{Type}, O: \operatorname{Type},\\J: \operatorname{Finset}\left(\mathbb{N}\right), K: \operatorname{Finset}\left(\mathbb{N}\right), m: \mathbb{N}, n: \mathbb{N},\\readout: \mathbb{N} \to \left(X \to O\right), T: X \to X,\\J \subseteq K \land m \leq n \Rightarrow\\\operatorname{observationSchedule}\left(J, m\right) \subseteq \operatorname{observationSchedule}\left(K, n\right) \land\\\operatorname{Indist}\left(K, n, readout, T\right) \subseteq \operatorname{Indist}\left(J, m, readout, T\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/BiaxialObservationRefinement.biaxial_observation_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation schedule is the existing set of index-time pairs whose index lies in the finite set and whose time is below the horizon.

Containment of index sets and ordering of horizons first include the smaller schedule in the larger schedule. This is the source's first public set relation.

The imported biaxial monotonicity theorem then reverses inclusion of the associated indistinguishability relations, providing the second public set relation without restating its proof.

## References

- Truth anchor: `D5/S3/Observer/Refinement/BiaxialObservationRefinement.biaxial_observation_refinement`
- Dependency: [D5/S3/Observer/Refinement/BiaxialMonotoneRefinement](BiaxialMonotoneRefinement.md)
