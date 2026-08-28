# Adjudication Stop Target Correctness

## Abstract

The adjudication stop target has an exact finite checker and guarded boundary behavior.

**Theorem 1.1 (The finite stop checker is exact and rejects vacuous boundary cases).**

$$\begin{gathered}(\operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget, InScope, O, D\right) \iff \operatorname{OrientedStopOnDecisionSet}\left(AdmTarget, InScope, O, D\right)) \land\\{}(\operatorname{AdjudicationStopTarget}\left(AdmTarget, InScope, O, K\right) \iff \operatorname{OrientedStop}\left(AdmTarget, InScope, O, K\right)) \land\\{}(\operatorname{stopCheck}\left(AdmTarget, InScope, O, D\right) = true \iff \operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget, InScope, O, D\right)) \land\\{}(\operatorname{settleStop}\left(AdmTarget, InScope, O, K\right) = true \iff \operatorname{AdjudicationStopTarget}\left(AdmTarget, InScope, O, K\right)) \land\\{}(\operatorname{settleStop}\left(AdmTarget, InScope, O, K\right) = false \iff \neg \operatorname{AdjudicationStopTarget}\left(AdmTarget, InScope, O, K\right)) \land\\{}(\operatorname{current}\left(D\right) = none \Rightarrow \neg \operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget, InScope, O, D\right)) \land\\{}(\operatorname{feasible}\left(D\right) = \emptyset \Rightarrow \neg \operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget, InScope, O, D\right)) \land\\{}(\forall a, (\operatorname{current}\left(D\right) = \operatorname{some}\left(a\right) \land \neg (a \in \operatorname{feasible}\left(D\right))) \Rightarrow \neg \operatorname{AdjudicationStopTargetOnDecisionSet}\left(AdmTarget, InScope, O, D\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/AdjudicationStopTargetCorrectness.adjudication_stop_target_correctness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary source types and the decidable premises in the Lean declaration, the named target is compared with the independently expanded oriented stop predicate, both at decision-set level and after projection from the canonical prospective commitment.

The Boolean checker matches on current first and then performs only decidable scans bounded by the sealed feasible Finset. Its success and failure values are both characterized by the named target.

The final three clauses separately rule out a missing current, an empty feasible set, and a current action outside that feasible set; thus a vacuous universal domain check cannot manufacture a stop.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/AdjudicationStopTargetCorrectness.adjudication_stop_target_correctness`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoFrontierStopDivergence](ParetoFrontierStopDivergence.md)
