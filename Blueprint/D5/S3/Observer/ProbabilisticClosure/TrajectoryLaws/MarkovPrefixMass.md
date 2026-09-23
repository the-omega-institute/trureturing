# Singleton prefix masses of a homogeneous Markov trajectory

## Abstract

Singleton prefix masses of a homogeneous Markov trajectory.

**Theorem 1.1 (Singleton prefix masses of a homogeneous Markov trajectory).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Singleton prefix masses of a homogeneous Markov trajectory*. URL: <https://github.com/TauCetiProject/TauCeti/tree/fbb1ce3c887a9697c1be346d135aed8b2932997a>.

*Commentary.*

For every measurable state space with measurable singletons, probability initial law, Markov transition kernel and natural prefix length, the singleton prefix mass equals the initial singleton mass times the product of transition singleton masses.

The statement uses Mathlib trajMeasure directly with the homogeneous history-reading kernel. Prefix length is arbitrary, and zero initial or transition masses are permitted. The prefix extension preserves the current state and its transition kernel.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton`
