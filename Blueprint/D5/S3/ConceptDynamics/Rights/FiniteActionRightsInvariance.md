# Finite Action Rights Invariance

## Abstract

Every finite sequence of certified atomic actions preserves the safe state set.

**Theorem 1.1 (Certified atomic actions generate finite safe processes).**

$$\forall X \in Type, U \in Type, S \in \operatorname{Set}\left(X\right), F \in U \to \left(X \to X\right),\; \left(\forall u \in U,\; \operatorname{MapsTo}\left(F\left(u\right), S, S\right)\right) \Rightarrow \left(\forall actions \in \operatorname{List}\left(U\right),\; \operatorname{MapsTo}\left((x \mapsto \operatorname{foldl}\left((x, u \mapsto F\left(u\right)\left(x\right)), x, actions\right)), S, S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Rights/FiniteActionRightsInvariance.finite_action_sequence_preserves_rights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let each action in a family map a designated safe set into itself. Folding any finite action list from left to right then maps every initially safe state back into the same safe set. The empty list is the identity case, and the inductive step applies the next atomic certificate before the remaining list certificate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Rights/FiniteActionRightsInvariance.finite_action_sequence_preserves_rights`
