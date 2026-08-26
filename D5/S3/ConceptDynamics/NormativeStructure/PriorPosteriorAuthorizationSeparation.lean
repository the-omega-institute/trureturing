/- GID: D5/S3/ConceptDynamics/NormativeStructure/PriorPosteriorAuthorizationSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/PriorPosteriorAuthorizationSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A change can revise the approval standard by which it is later authorized. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-26):
   * Repository searches for posterior approval, prior authorization, action
     preferences, and approval standards found no exact frozen theorem or
     canonical authorization semantics for preference-changing processes.
   * Body-shape searches for an approval predicate applied to the action
     preference before and after a change found only the withdrawn local-let
     encoding. No D5 primitive has the definition introduced below.
   * Pinned Mathlib searches for posterior approval, prior authorization,
     approval standards, and action preferences found no exact declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.PriorPosteriorAuthorizationSeparation

/-- A state authorizes a change when its current approval standard accepts the
action-preference transition produced by that change. -/
def modificationAuthorized {State Action : Type*}
    (actionPreference : State -> Action)
    (approvalStandard : State -> Action -> Action -> Prop)
    (change : State -> State) (state : State) : Prop :=
  approvalStandard state (actionPreference state) (actionPreference (change state))

/-- There is a subject state and a change that revises both the action
preference and the approval standard. The original state does not authorize
the change, while the resulting state authorizes that same change. -/
theorem posterior_approval_authorization_separation :
    ∃ actionPreference : Bool × Bool -> Bool,
      ∃ approvalStandard : Bool × Bool -> Bool -> Bool -> Prop,
        ∃ change : Bool × Bool -> Bool × Bool,
          ∃ original : Bool × Bool,
            actionPreference (change original) ≠ actionPreference original ∧
              approvalStandard (change original) ≠ approvalStandard original ∧
              ¬ modificationAuthorized actionPreference approvalStandard change original ∧
              modificationAuthorized actionPreference approvalStandard change
                  (change original) ∧
              ¬ (modificationAuthorized actionPreference approvalStandard change
                    (change original) ->
                  modificationAuthorized actionPreference approvalStandard change
                    original) := by
  let actionPreference : Bool × Bool -> Bool := fun state => state.1
  let approvalStandard : Bool × Bool -> Bool -> Bool -> Prop :=
    fun state before after => state.2 = true ∧ before ≠ after
  let change : Bool × Bool -> Bool × Bool :=
    fun state => (!state.1, !state.2)
  let original : Bool × Bool := (false, false)
  refine ⟨actionPreference, approvalStandard, change, original, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun equalPreference => Bool.false_ne_true equalPreference.symm
  · intro equalStandards
    have accepted : approvalStandard (change original) false true :=
      ⟨rfl, Bool.false_ne_true⟩
    rw [equalStandards] at accepted
    exact Bool.false_ne_true accepted.1
  · intro priorAuthorization
    exact Bool.false_ne_true priorAuthorization.1
  · exact ⟨rfl, fun equalPreference => Bool.false_ne_true equalPreference.symm⟩
  · intro posteriorImpliesPrior
    have priorAuthorization := posteriorImpliesPrior
      ⟨rfl, fun equalPreference => Bool.false_ne_true equalPreference.symm⟩
    exact Bool.false_ne_true priorAuthorization.1

#print axioms posterior_approval_authorization_separation

end D5.S3.ConceptDynamics.NormativeStructure.PriorPosteriorAuthorizationSeparation
