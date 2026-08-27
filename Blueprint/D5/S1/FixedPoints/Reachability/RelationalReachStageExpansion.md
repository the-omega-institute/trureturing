# Relational Reach Stage Expansion

## Abstract

A relation-generated reachability operator expands from the empty and initial stages through every finite successor stage.

**Theorem 1.1 (Relational reachability expands through all finite stages).**

$$\forall X, J: Type,\\{}R: \operatorname{Set}\left(X \times X\right), I_{0}: \operatorname{Set}\left(X\right), A: J \to \operatorname{Set}\left(X\right),\\{}\operatorname{image}_{R}(\operatorname{union}_{i\in J} A(i)) = \operatorname{union}_{i\in J} \operatorname{image}_{R}(A(i)) \land\\{}\operatorname{lfp}\left((S \mapsto I_{0} \operatorname{union} \operatorname{image}_{R}(S))\right) = \operatorname{union}_{n\in \mathbb{N}} (S \mapsto I_{0} \operatorname{union} \operatorname{image}_{R}(S))^{[n]}(\emptyset) \land\\{}(S \mapsto I_{0} \operatorname{union} \operatorname{image}_{R}(S))^{[0]}(\emptyset) = \emptyset \land\\{}(S \mapsto I_{0} \operatorname{union} \operatorname{image}_{R}(S))^{[1]}(\emptyset) = I_{0} \land\\{}\forall n\in \mathbb{N}, (S \mapsto I_{0} \operatorname{union} \operatorname{image}_{R}(S))^{[n + 1]}(\emptyset) = I_{0} \operatorname{union} \operatorname{image}_{R}((S \mapsto I_{0} \operatorname{union} \operatorname{image}_{R}(S))^{[n]}(\emptyset)).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/Reachability/RelationalReachStageExpansion.finite_step_expansion_with_initial_stages` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transition relation R and initial set I0 construct the canonical operator Phi(S) = I0 union image_R(S). No reachability object is defined by the conclusion it is meant to satisfy.

The frozen finite-step theorem supplies arbitrary-union preservation and identifies the least fixed point with the union of all finite iterates from the empty set.

The restored public clauses expose the zeroth and first iterates and the successor recurrence. Thus every later stage keeps I0 and adds one further direct relational image.

Repository body-shape search found the canonical reachStep primitive and no existing public theorem carrying all restored stage clauses. Pinned Mathlib's iterate identities discharge those clauses.

## References

- Truth anchor: `D5/S1/FixedPoints/Reachability/RelationalReachStageExpansion.finite_step_expansion_with_initial_stages`
- Dependency: [D5/S1/FixedPoints/RelationalReachExpansion](../RelationalReachExpansion.md)
