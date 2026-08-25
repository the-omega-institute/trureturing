# Predictive Completion Monotonicity

## Abstract

Predictive completion preserves the refinement order of readouts.

**Theorem 1.1 (Predictive completion preserves refinement).**

$$\begin{gathered}\forall X, O, P: \operatorname{Type},\\{}F: X \to X, q: X \to O, r: X \to P,\\{}(\forall x, y: X, (r(x) = r(y) \Rightarrow q(x) = q(y)) \land (predictiveProjection(F, r)(x) = predictiveProjection(F, r)(y) \Rightarrow predictiveProjection(F, q)(x) = predictiveProjection(F, q)(y))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone.predictive_completion_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The premise says that equality under the finer readout r implies equality under q. This is exactly inclusion of the two current readout kernels.

The all-iterate congruence kernel is monotone under relation inclusion. Quotient equality for r therefore yields the corresponding kernel relation for q, and the quotient soundness theorem concludes.

No inhabitedness, finiteness, or update assumptions are used; the empty, singleton, constant-update, identity-readout, and zero-step examples are checked in the Lean module.

**Lemma 1.2 (The refinement premise is necessary).**

$$\neg \forall x, y: Bool, predictiveProjection(id, \operatorname{const}(Unit))(x) = predictiveProjection(id, \operatorname{const}(Unit))(y) \Rightarrow predictiveProjection(id, id)(x) = predictiveProjection(id, id)(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone.refinement_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Bool states with identity dynamics, a constant Unit readout makes the two quotient classes equal, while the identity Bool readout keeps true and false distinct.

Thus the conclusion fails when the relation-inclusion premise is removed. This concrete counterexample is the required audit of the only non-definitional hypothesis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone.predictive_completion_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone.refinement_hypothesis_is_necessary`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient](MinimalPredictiveCompletionQuotient.md)
