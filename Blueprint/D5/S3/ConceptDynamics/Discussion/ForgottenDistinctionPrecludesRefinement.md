# Forgotten Distinction Precludes Refinement

## Abstract

A future readout that forgets a past distinction cannot refine the past readout.

**Theorem 1.1 (Forgetting a distinction obstructs refinement).**

$$\forall X \in Type, C \in Type, D \in Type, past \in \operatorname{Concept}\left(X, C\right), future \in \operatorname{Concept}\left(X, D\right), x \in X, y \in X,\; \left(past\left(x\right) \ne past\left(y\right) \land future\left(x\right) = future\left(y\right)\right) \Rightarrow \left(\neg \operatorname{Refines}\left(past, future\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Discussion/ForgottenDistinctionPrecludesRefinement.forgotten_distinction_precludes_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The past and future concepts are arbitrary readouts on the same state space. Two states have different past readouts but the same future readout, which directly records that the old distinction was lost.

If the future refined the past, the canonical refinement factor would transport equality of the future readouts back to equality of the past readouts, contradicting the displayed distinction.

The proof imports the existing refinement-preservation theorem and takes its contrapositive. No new concept or refinement relation is defined.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Discussion/ForgottenDistinctionPrecludesRefinement.forgotten_distinction_precludes_refinement`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RefinementShrinksIndistinguishability](../RefinementFactorization/RefinementShrinksIndistinguishability.md)
