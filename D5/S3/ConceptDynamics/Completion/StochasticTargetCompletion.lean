/- GID: D5/S3/ConceptDynamics/Completion/StochasticTargetCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/StochasticTargetCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional-law completion is the least prediction-sufficient conservative refinement. -/

import D5.S3.ConceptDynamics.Completion.TargetClosureReflection
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-24):
   * Exact repository hit `target_closure_is_least_target_sufficient_refinement`
     states the full least sufficient refinement theorem and is applied directly.
   * Exact family hits `Concept`, `Refines`, `targetClosure`, and
     `TargetSufficient` are imported from the completion family; no sibling
     primitive is redeclared.
   * Pinned-Mathlib exact hit `PMF` in
     `ProbabilityMassFunction.Basic` supplies the discrete conditional-law carrier.
   * `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.StochasticTargetCompletion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Completion.TargetClosureOperator
open D5.S3.ConceptDynamics.Completion.TargetClosureReflection

set_option linter.unusedFintypeInType false

/-- Joining a finite-state concept with its complete conditional-law kernel is
prediction-sufficient, preserves the original concept, and is below every
other prediction-sufficient refinement of that concept. -/
theorem stochastic_target_completion_is_least
    {X C Y : Type*} [Fintype X]
    (concept : Concept X C) (kernel : X -> PMF Y) :
    TargetSufficient (targetClosure concept kernel) kernel /\
      Refines concept (targetClosure concept kernel) /\
      forall {D : Type*} (candidate : Concept X D),
        Refines concept candidate -> TargetSufficient candidate kernel ->
          Refines (targetClosure concept kernel) candidate := by
  rcases target_closure_is_least_target_sufficient_refinement concept kernel with
    ⟨sufficient, conservative, least⟩
  exact ⟨sufficient, conservative, fun candidate refined predicts =>
    least candidate predicts refined⟩

#print axioms stochastic_target_completion_is_least

end D5.S3.ConceptDynamics.Completion.StochasticTargetCompletion
