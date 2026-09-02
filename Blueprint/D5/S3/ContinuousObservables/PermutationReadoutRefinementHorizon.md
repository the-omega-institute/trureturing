# Permutation Readout Refinement and Horizon Bounds

## Abstract

Readout refinement grows permutation horizons up to the full cyclic-orbit bound, while changing the update changes that bound.

**Theorem 1.1 (Readout refinement stays within the orbit bound).**

$$\forall I, tau, tauPrime \in \operatorname{EquivPerm}(I), o \in I,\ (\forall A \subseteq \operatorname{Read}(tau), \operatorname{H}(tau, A, o) \subseteq I \setminus \operatorname{Orb}(tau, o)) \land\ (\forall A, B \subseteq \operatorname{Read}(tau), A \subseteq B \Rightarrow \operatorname{H}(tau, A, o) \subseteq \operatorname{H}(tau, B, o)) \land\ \operatorname{H}(tau, \operatorname{Read}(tau), o) = I \setminus \operatorname{Orb}(tau, o) \land\ (\forall y \in \operatorname{Orb}(tauPrime, o) \setminus \operatorname{Orb}(tau, o), y \in \operatorname{H}(tau, \operatorname{Read}(tau), o) \land \operatorname{d}(tauPrime, o, y) < \infty) \land\ (\exists sigma \in \operatorname{EquivPerm}(Bool), C, D \subseteq \operatorname{Read}(sigma), C \subseteq D \land \operatorname{H}(sigma, C, false) = \emptyset \land true \in \operatorname{H}(sigma, D, false)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/PermutationReadoutRefinementHorizon.permutation_readout_refinement_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed permutation, every chosen family of bounded unit-edge readouts has horizon inside the complement of the origin's cyclic orbit. Inclusion of readout families enlarges the horizon, and the full admissible family attains the orbit-complement bound.

Changing the permutation changes the orbit bound: a point outside the old orbit but inside the new orbit has infinite old full-family distance and finite new full-family distance.

The strict-refinement example corrects the literal source example. One bounded orbit indicator has only finite oscillation, so it cannot by itself create infinite distance. The formal witness adjoins every real scalar multiple of the indicator; their supremum is infinite.

## References

- Truth anchor: `D5/S3/ContinuousObservables/PermutationReadoutRefinementHorizon.permutation_readout_refinement_horizon`
- Dependency: [D5/S3/ContinuousObservables/PermutationOrbitHorizon](PermutationOrbitHorizon.md)
