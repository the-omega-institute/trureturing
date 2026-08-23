/- GID: D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Opposite Boolean causal directions agree observationally but separate under do(X). -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'observation_strictly_weaker_than_intervention' D5
     Golden/Frozen/accepted` found no existing declaration.
   * Repository searches for structural causal models, causal directions, and
     observational/interventional separation found only unrelated intervention closure,
     fairness, and reachability results; none compares two causal models with equal
     observational behavior and unequal intervention behavior.
   * The pinned Mathlib search for causal models, interventions, counterfactuals, and
     structural equations found no reusable formal declaration. The proof therefore uses
     only Boolean evaluation, products, function extensionality, and congruence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

/-- The causal direction in a two-variable acyclic structural model. -/
inductive CausalDirection where
  | xCausesY
  | yCausesX

/-- A deterministic Boolean structural causal model with one root mechanism and one
child mechanism. The direction determines which variable is the root. -/
structure DeterministicBoolSCM where
  direction : CausalDirection
  root : Bool -> Bool
  child : Bool -> Bool

/-- The observable joint response `(X, Y)` to an exogenous Boolean input. -/
def Obs (model : DeterministicBoolSCM) : Bool -> Bool × Bool :=
  fun u =>
    match model.direction with
    | .xCausesY =>
        let x := model.root u
        (x, model.child x)
    | .yCausesX =>
        let y := model.root u
        (model.child y, y)

/-- The joint response after `do(X := x)`, indexed by the imposed value and the
exogenous input. Replacing the X equation affects Y exactly when X causes Y. -/
def Int (model : DeterministicBoolSCM) : Bool -> Bool -> Bool × Bool :=
  fun x u =>
    match model.direction with
    | .xCausesY => (x, model.child x)
    | .yCausesX => (x, model.root u)

/-- The model `X := U; Y := X`. -/
def xCausesYModel : DeterministicBoolSCM where
  direction := .xCausesY
  root := id
  child := id

/-- The model `Y := U; X := Y`. -/
def yCausesXModel : DeterministicBoolSCM where
  direction := .yCausesX
  root := id
  child := id

/-- Opposite causal directions can have identical observational behavior while the
intervention `do(X := x)` distinguishes them. -/
theorem observation_strictly_weaker_than_intervention :
    ∃ M N : DeterministicBoolSCM, Obs M = Obs N ∧ Int M ≠ Int N := by
  refine ⟨xCausesYModel, yCausesXModel, ?_, ?_⟩
  · funext u
    rfl
  · intro interventionsEqual
    have equalAtWitness := congrFun (congrFun interventionsEqual false) true
    have false_eq_true : false = true := by
      simpa [Int, xCausesYModel, yCausesXModel] using congrArg Prod.snd equalAtWitness
    exact Bool.false_ne_true false_eq_true

example : Obs xCausesYModel true = (true, true) := rfl

example : Int xCausesYModel false true ≠ Int yCausesXModel false true := by
  decide

#print axioms observation_strictly_weaker_than_intervention

end D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
