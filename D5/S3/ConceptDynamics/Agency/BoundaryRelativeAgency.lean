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
choice, and suppose that variable determines action. If the observer interface
recovers the decision variable, it also recovers action, so the variable can be
an internal reason. Conversely, a pair hidden by the observer but separated by
both the decision and action witnesses an inaccessible decision variable and
precludes action control from descending to that observer boundary. -/
theorem boundary_relative_agency
    {History ObserverState PastChoice Decision Action : Type*}
    (observer : History -> ObserverState)
    (pastChoice : History -> PastChoice)
    (update : PastChoice -> Decision)
    (action : History -> Action)
    (decisionControlsAction :
      ControlPrinciple (update ∘ pastChoice) action) :
    (ControlPrinciple observer (update ∘ pastChoice) ->
        ControlPrinciple observer action) /\
      forall left right : History,
        observer left = observer right ->
          update (pastChoice left) ≠ update (pastChoice right) ->
          action left ≠ action right ->
          MoralLuckWitness observer (update ∘ pastChoice) /\
            Not (ControlPrinciple observer action) := by
  rcases decisionControlsAction with ⟨actionFromDecision, actionFactors⟩
  constructor
  · rintro ⟨decisionFromObserver, decisionFactors⟩
    refine ⟨actionFromDecision ∘ decisionFromObserver, ?_⟩
    rw [actionFactors, decisionFactors]
    exact (Function.comp_assoc actionFromDecision decisionFromObserver observer).symm
  · intro left right sameObserver differentDecision differentAction
    refine ⟨⟨left, right, sameObserver, differentDecision⟩, ?_⟩
    rintro ⟨actionFromObserver, actionFactors⟩
    apply differentAction
    rw [actionFactors]
    simp only [Function.comp_apply, sameObserver]

#print axioms boundary_relative_agency

end D5.S3.ConceptDynamics.Agency.BoundaryRelativeAgency
