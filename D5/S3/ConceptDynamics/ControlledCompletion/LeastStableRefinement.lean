/- GID: D5/S3/ConceptDynamics/ControlledCompletion/LeastStableRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ControlledCompletion/LeastStableRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Action-word completion is the least interface stable under every generating action. -/

import D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality

/- Library-search audit trail (2026-08-25):
   * Exact repository searches for controlled completion, action stability,
     and least stable refinement found the canonical `DynClosure` and
     `InterventionClosed` primitives in `DynamicClosureMinimality`.
   * That module proves the three required clauses separately as
     `concept_refines_dynamic_closure`,
     `dynamic_closure_is_intervention_closed`, and
     `dynamic_closure_is_least`; all three are applied directly below.
   * No repository theorem bundles all three public least-element clauses.
     Pinned Mathlib searches for intervention closure and least stable
     refinements found no exact theorem. -/

namespace D5.S3.ConceptDynamics.ControlledCompletion.LeastStableRefinement

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.DynamicClosureMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The finite-action-word completion refines the original interface, is stable
under every generating action, and refines every other interface with those
properties. -/
theorem controlled_completion_is_least_stable_refinement
    {X A U : Type*} (q : Concept X A) (intervene : U -> X -> X) :
    Refines q (DynClosure q intervene) ∧
      InterventionClosed (DynClosure q intervene) intervene ∧
      ∀ {B : Type*} (candidate : Concept X B),
        Refines q candidate ->
        InterventionClosed candidate intervene ->
        Refines (DynClosure q intervene) candidate := by
  refine ⟨concept_refines_dynamic_closure q intervene,
    dynamic_closure_is_intervention_closed q intervene, ?_⟩
  intro B candidate refinement closed
  exact dynamic_closure_is_least q intervene candidate refinement closed

#print axioms controlled_completion_is_least_stable_refinement

end D5.S3.ConceptDynamics.ControlledCompletion.LeastStableRefinement
