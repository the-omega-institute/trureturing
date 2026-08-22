/- GID: D5/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full-action identity refines passive identity, and the reverse can fail. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishability

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'control_identity_refines_passive' D5 Golden/Frozen/accepted`
     found no repository declaration or accepted duplicate.
   * `rg -n 'control|passive|quotient|Dyn|dynamic.*completion'
     D5/S3/ConceptDynamics/ --glob '*.lean'` found
     `ActionExpansionIndistinguishability.action_expansion_shrinks_indistinguishability`;
     it is reused for the relation-level inclusion below.
   * `ConceptJoinUniversal.Refines` is the canonical factorization order and is reused.
     No existing result constructs the required restriction factor or the strict finite
     counterexample; those use subtype restriction, function extensionality, and `Bool`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.ControlIdentityRefinesPassive

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishability

/-- The identity induced by an action family records every subsequent public readout. -/
def actionIdentity {Action State Output : Type _} (allowed : Set Action)
    (act : Action -> State -> State) (observe : Concept State Output) :
    Concept State ({action // action ∈ allowed} -> Output) :=
  fun state action => observe (act action.1 state)

/-- Restricting all control actions to the passive subfamily gives both the
factorization order and the corresponding inclusion of indistinguishable pairs. -/
theorem control_identity_refines_passive
    {Action State Output : Type _} (passive control : Set Action)
    (act : Action -> State -> State) (observe : Concept State Output)
    (hPassive : passive ⊆ control) :
    Refines (actionIdentity passive act observe) (actionIdentity control act observe) ∧
      actionIndistinguishability control act observe ⊆
        actionIndistinguishability passive act observe := by
  constructor
  · refine ⟨fun identity action =>
      identity ⟨action.1, hPassive action.2⟩, ?_⟩
    funext state action
    rfl
  · exact action_expansion_shrinks_indistinguishability
      passive control act observe hPassive

/-- The reverse refinement can fail even with two states and a nonempty passive
action family: the passive action erases the state, while the added action preserves it. -/
theorem reverse_control_refinement_can_fail :
    let passive : Set Bool := {false}
    let control : Set Bool := Set.univ
    let act : Bool -> Bool -> Bool := fun action state => if action then state else false
    let observe : Concept Bool Bool := id
    passive ⊆ control ∧
      Refines (actionIdentity passive act observe) (actionIdentity control act observe) ∧
      ¬Refines (actionIdentity control act observe) (actionIdentity passive act observe) := by
  dsimp
  constructor
  · exact Set.subset_univ _
  constructor
  · exact (control_identity_refines_passive _ _ _ _ (Set.subset_univ _)).1
  · rintro ⟨factor, hFactor⟩
    have passiveSame :
        actionIdentity ({false} : Set Bool)
            (fun action state => if action then state else false) id false =
          actionIdentity ({false} : Set Bool)
            (fun action state => if action then state else false) id true := by
      funext action
      have actionFalse : action.1 = false := by
        exact Set.mem_singleton_iff.mp action.2
      simp [actionIdentity, actionFalse]
    have controlSame :
        actionIdentity (Set.univ : Set Bool)
            (fun action state => if action then state else false) id false =
          actionIdentity (Set.univ : Set Bool)
            (fun action state => if action then state else false) id true := by
      calc
        _ = factor
            (actionIdentity ({false} : Set Bool)
              (fun action state => if action then state else false) id false) :=
          congrFun hFactor false
        _ = factor
            (actionIdentity ({false} : Set Bool)
              (fun action state => if action then state else false) id true) :=
          congrArg factor passiveSame
        _ = _ := (congrFun hFactor true).symm
    have distinguishes := congrFun controlSame ⟨true, Set.mem_univ true⟩
    simp [actionIdentity] at distinguishes

example :
    Refines
      (actionIdentity ({false} : Set Bool)
        (fun (action state : Bool) => if action then state else false) id)
      (actionIdentity Set.univ
        (fun (action state : Bool) => if action then state else false) id) := by
  exact (control_identity_refines_passive _ _ _ _ (Set.subset_univ _)).1

#print axioms control_identity_refines_passive

end D5.S3.ConceptDynamics.Control.ControlIdentityRefinesPassive
