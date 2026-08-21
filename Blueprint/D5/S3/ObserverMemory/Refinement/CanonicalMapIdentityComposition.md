# Canonical Map Identity and Composition

## Abstract

Canonical predictive-completion maps satisfy identity and composition.

**Theorem 1.1 (Canonical maps compose and have identities).**

$$\forall q, kappa_{q, q} = id \land\ \forall q, r, s,\ \operatorname{Refines}\left(q, r\right) \land \operatorname{Refines}\left(r, s\right) \Rightarrow kappa_{q, s} = kappa_{r, s}(kappa_{q, r}(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/CanonicalMapIdentityComposition.canonical_map_identity_and_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed finite nonempty state carrier and a deterministic update, each readout defines a predictive completion as the quotient by equality of all future readout values.

When one readout factors through another, the existing quotient factor construction supplies the canonical map between their completed state spaces and its equation on every source projection.

Applying that projection equation first to the identity factorization and then to a chain of two factorizations proves the displayed identity and composition laws by quotient induction.

Repository search found and directly applied the exact declarations completionFactor and completion_factor_projection. No imported theorem packaged both displayed map laws.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/CanonicalMapIdentityComposition.canonical_map_identity_and_composition`
- Dependency: [D5/S3/ObserverMemory/Refinement/CascadeCompletion](CascadeCompletion.md)
