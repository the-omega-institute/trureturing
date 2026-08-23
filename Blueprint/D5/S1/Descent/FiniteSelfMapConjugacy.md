# Finite Self-Map Conjugacy

## Abstract

Conjugacy preserves cycle counts, and cycle type completely classifies finite permutations.

**Theorem 1.1 (Conjugacy preserves every cycle-length multiplicity).**

$$\forall Y, Z: \operatorname{Type},\ [\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(Z\right)],\ tau: Y \to Y, sigma: Z \to Z,\ relabel: Y \equiv Z,\ \operatorname{Conjugates}\left(tau, sigma, relabel\right) \Rightarrow \forall n \in \mathbb{N},\ \operatorname{cycleLengthMultiplicity}\left(tau, n\right) = \operatorname{cycleLengthMultiplicity}\left(sigma, n\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Descent/FiniteSelfMapConjugacy.finite_self_map_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An equivalence that intertwines two finite self-maps carries every iterate of the first map to the corresponding iterate of the second. It therefore preserves the minimal period of each point.

For every natural number n, the relabeling restricts to a bijection between the points of minimal period n. The two filtered finite sets have the same cardinality, so dividing by n gives equal cycle-length multiplicities. At n = 0 both multiplicities are zero, and transient points do not contribute.

This is an invariance statement for arbitrary finite self-maps, not a classification theorem: cycle counts do not record the transient trees attached to the cycles.

**Theorem 1.2 (Cycle type completely classifies finite permutations).**

$$\forall Y: \operatorname{Type},\ [\operatorname{Fintype}\left(Y\right)], [\operatorname{DecidableEq}\left(Y\right)],\ tau, sigma: \operatorname{Perm}\left(Y\right),\ \operatorname{cycleType}\left(tau\right) = \operatorname{cycleType}\left(sigma\right) \iff \exists relabel: \operatorname{Perm}\left(Y\right),\ \operatorname{Conjugates}\left(tau, sigma, relabel\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Descent/FiniteSelfMapConjugacy.permutation_cycle_type_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two permutations of the same finite set have equal cycle type exactly when a permutation of the underlying set relabels one into the other. The relabeling is exhibited explicitly and intertwines the two permutation actions pointwise.

Because a permutation has no transient points, its cycle decomposition contains the whole dynamical system. Thus cycle type is a complete conjugacy invariant in the permutation case, in contrast with the one-way invariant for general finite self-maps.

## References

- Truth anchor: `D5/S1/Descent/FiniteSelfMapConjugacy.finite_self_map_conjugacy`
- Truth anchor: `D5/S1/Descent/FiniteSelfMapConjugacy.permutation_cycle_type_complete`
