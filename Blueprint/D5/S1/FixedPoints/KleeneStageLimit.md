# Kleene Stage Limit

## Abstract

An omega-continuous operator's least fixed point is the supremum of its finite stages.

**Theorem 1.1 (The least fixed point is reached as a stage supremum).**

$$\begin{gathered}\forall \alpha: \operatorname{Type}, [\operatorname{CompleteLattice}\left(\alpha\right)],\\{}f: \alpha \to_{o} \alpha, \omega\operatorname{ScottContinuous}(f) \Rightarrow \operatorname{lfp}(f)=\operatorname{sup}_{n\in \mathbb{N}} f^{[n]}(\operatorname{bottom}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/KleeneStageLimit.inductive_definition_is_supremum_of_stages` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be an omega-Scott-continuous order endomorphism of a complete lattice. Its least fixed point is the supremum of the finite iterates of f beginning at the bottom element.

The Lean declaration is a thin repository wrapper around the exact pinned Mathlib theorem fixedPoints.lfp_eq_sSup_iterate. Repository searches found no equivalent D5 declaration; LeanSearch's API endpoint returned HTTP 404.

This closes only the Kleene finite-stage clause of source theorem 7.6. It does not assert the atom's analytic-continuation analogy, independence claim, or free-choice interpretation.

## References

- Truth anchor: `D5/S1/FixedPoints/KleeneStageLimit.inductive_definition_is_supremum_of_stages`
