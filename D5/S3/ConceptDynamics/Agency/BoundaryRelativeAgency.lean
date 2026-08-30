/- GID: D5/S3/ConceptDynamics/Agency/BoundaryRelativeAgency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/BoundaryRelativeAgency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observer accessibility makes control internal; a blind boundary leaves it external. -/

import D5.S3.ConceptDynamics.MoralLuck.MoralLuckDescent

/- Library-search audit trail (2026-08-31):
   * Exact repository hits `ControlPrinciple` and `MoralLuckWitness` are the
     canonical factorization and same-fiber obstruction predicates; they are
     imported instead of redeclared.
   * Searches for boundary-relative agency, internal reasons, external control,
     observer inaccessibility, and past-choice updates found no exact D5 theorem.
   * Pinned Mathlib hits `Function.comp_assoc` and
     `Function.FactorsThrough.comp_left` provide the generic composition shape,
     but no theorem packages both sides of the boundary contrast. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.BoundaryRelativeAgency

open D5.S3.ConceptDynamics.MoralLuck.MoralLuckDescent

/-- Let one decision variable be constructed by updating a recorded past
choice, and let an explicit control map determine action from that variable.
If the observer interface recovers the decision variable, composition recovers
action. Independently, if the observer hides two distinct decision values and
the control map is injective, action cannot factor through that interface. -/
theorem boundary_relative_agency
    {History ObserverState PastChoice Decision Action : Type*}
    (observer : History -> ObserverState)
    (pastChoice : History -> PastChoice)
    (update : PastChoice -> Decision)
    (action : History -> Action)
    (actionFromDecision : Decision -> Action)
    (decisionControlsAction :
      action = actionFromDecision ∘ (update ∘ pastChoice)) :
    (ControlPrinciple observer (update ∘ pastChoice) ->
        ControlPrinciple observer action) /\
      (MoralLuckWitness observer (update ∘ pastChoice) ->
        Function.Injective actionFromDecision ->
          Not (ControlPrinciple observer action)) := by
  fail_if_success
    ((try intros); simp only [ControlPrinciple, MoralLuckWitness]; assumption)
  constructor
  · fail_if_success rfl
    rintro ⟨decisionFromObserver, decisionFactors⟩
    refine ⟨actionFromDecision ∘ decisionFromObserver, ?_⟩
    rw [decisionControlsAction, decisionFactors]
    exact (Function.comp_assoc actionFromDecision decisionFromObserver observer).symm
  · fail_if_success rfl
    rintro ⟨left, right, sameObserver, differentDecision⟩
    intro actionRelevant
    rintro ⟨actionFromObserver, actionFactors⟩
    apply differentDecision
    apply actionRelevant
    have sameAction : action left = action right := by
      rw [actionFactors]
      simp only [Function.comp_apply, sameObserver]
    simpa only [decisionControlsAction, Function.comp_apply] using sameAction

#print axioms boundary_relative_agency

end D5.S3.ConceptDynamics.Agency.BoundaryRelativeAgency
