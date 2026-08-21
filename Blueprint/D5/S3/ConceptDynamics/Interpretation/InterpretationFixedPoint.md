# Context-Relative Interpretation Fixed Points

## Abstract

Interpretation fixed points are relative to context; context variation can change them, while objectivity carries an invariant-factor proof.

**Theorem 1.1 (Conceptual equivalence and stable interpretation reach a fixed point).**

$$\operatorname{ConceptEquivalent}(C_{n+1}, C_{n}) \land I_{\kappa}(C_{n+1}) = I_{\kappa}(C_{n}) \Rightarrow \operatorname{RelativeFixedPoint}(\kappa, n).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.conceptual_equivalence_and_stability_reach_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a text, reader-admission policy, background, evaluation goal, and interpretation rule. If the next concept stage is conceptually equivalent to the current stage and both stages have the same interpreted result in that context, the stage satisfies the definition of a relative interpretation fixed point.

**Theorem 1.2 (Context parameters can select distinct fixed meanings).**

$$\operatorname{sameTextAndRule}(\kappa_{0}, \kappa_{1}) \land \operatorname{differentAdmissionBackgroundGoal}(\kappa_{0}, \kappa_{1}) \land\ \operatorname{FixedMeaning}(\kappa_{0}, m_{0}) \land \operatorname{FixedMeaning}(\kappa_{1}, m_{1}) \land\ m_{0} \neq m_{1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A two-context finite model holds the text and interpretation rule fixed while changing reader admission, background, and evaluation goal. The selected fixed meaning records those three parameters, so the two contextual fixed meanings are unequal.

This is an existential witness for the source word 'may': context variation can produce different fixed points. It does not claim that every pair of contexts must disagree.

**Theorem 1.3 (Objectivity requires an invariant common factor).**

$$\operatorname{ObjectiveClaim}(F, q) \Rightarrow \exists a,\ \forall \kappa, m,\ \operatorname{FixedMeaning}(\kappa, m) \Rightarrow q(m) = a.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.objective_claim_requires_invariant_common_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An objective interpretation claim is proof-carrying. It consists of a proposed factor value and a proof that every contextual fixed meaning maps to that same value. The theorem exposes exactly this invariant common factor.

Together the three declarations cover every independent source clause: the relative fixed-point definition, possible contextual nonuniqueness, and the invariant-factor obligation for objective interpretation. No source clause is claimed beyond these forms.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.conceptual_equivalence_and_stability_reach_fixed_point`
- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points`
- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.objective_claim_requires_invariant_common_factor`
