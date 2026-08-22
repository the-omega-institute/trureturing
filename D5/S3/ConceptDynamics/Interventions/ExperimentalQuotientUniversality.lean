/- GID: D5/S3/ConceptDynamics/Interventions/ExperimentalQuotientUniversality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/ExperimentalQuotientUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Intervention traces have the canonical empirical quotient universal property. -/

import D5.S3.ConceptDynamics.EmpiricalIdentifiability

/- Library-search audit trail (2026-08-22):
   * Exact repository family hits `empiricalSetoid`, `EmpiricalQuotient`, and
     `empiricalClass` are imported from `EmpiricalIdentifiability` rather than
     redeclared.
   * Exact repository theorem `empirical_identifiability` supplies unique descent
     precisely from constancy on all protocol-outcome fibers and is applied to
     both public clauses below.
   * Repository searches found no existing intervention/readout trace primitive,
     so `experimentTrace` constructs that source object recursively here.
   * Pinned quotient constructors are encapsulated by the exact imported theorem;
     Loogle and LeanSearch executables were absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.ExperimentalQuotientUniversality

open D5.S3.ConceptDynamics.EmpiricalIdentifiability

/-- The public observation trajectory produced by a finite sequence of allowed
interventions, including the observation before the first intervention. -/
def experimentTrace {Action State Observation : Type _}
    (intervene : Action -> State -> State) (observe : State -> Observation) :
    List Action -> State -> List Observation
  | [], state => [observe state]
  | action :: remaining, state =>
      observe state ::
        experimentTrace intervene observe remaining (intervene action state)

/-- Every allowed intervention trace descends uniquely to the canonical empirical
quotient. Conversely, any target that is constant on every empirical class also
descends uniquely, so empirical targets are exactly functions on that quotient. -/
theorem experimental_quotient_universality
    {Action State Observation Target : Type _}
    (intervene : Action -> State -> State)
    (observe : State -> Observation)
    (target : State -> Target) :
    (∀ actions : List Action,
      ∃! descend :
          EmpiricalQuotient (experimentTrace intervene observe) -> List Observation,
        experimentTrace intervene observe actions =
          descend ∘ empiricalClass (experimentTrace intervene observe)) ∧
    ((∀ ⦃x y : State⦄,
        (∀ actions : List Action,
          experimentTrace intervene observe actions x =
            experimentTrace intervene observe actions y) ->
          target x = target y) ->
      ∃! descend : EmpiricalQuotient (experimentTrace intervene observe) -> Target,
        target = descend ∘ empiricalClass (experimentTrace intervene observe)) := by
  constructor
  · intro actions
    exact
      (empirical_identifiability
        (experimentTrace intervene observe)
        (experimentTrace intervene observe actions)).1.mpr (by
          intro x y tracesEqual
          exact tracesEqual actions)
  · intro targetConstant
    exact
      (empirical_identifiability
        (experimentTrace intervene observe) target).1.mpr targetConstant

/-- The recursive trace records the initial observation and then each observation
after the successive interventions. -/
example :
    experimentTrace (fun (_ : Unit) (state : Bool) => !state) id
      [(), ()] false = [false, true, false] := by
  rfl

/-- A constant target satisfies the converse premise and therefore has its
unique factor through the canonical quotient. -/
example :
    let intervene : Unit -> Bool -> Bool := fun _ state => state
    let observe : Bool -> Unit := fun _ => ()
    let target : Bool -> Unit := fun _ => ()
    ∃! descend : EmpiricalQuotient (experimentTrace intervene observe) -> Unit,
      target = descend ∘ empiricalClass (experimentTrace intervene observe) := by
  dsimp
  apply (experimental_quotient_universality
    (fun _ : Unit => id) (fun _ : Bool => ()) (fun _ : Bool => ())).2
  intro x y tracesEqual
  rfl

/-- When all traces are constant but a target distinguishes two states, no map
from the canonical empirical quotient can represent that target. -/
example :
    let intervene : Unit -> Bool -> Bool := fun _ state => state
    let observe : Bool -> Unit := fun _ => ()
    ¬∃ descend : EmpiricalQuotient (experimentTrace intervene observe) -> Bool,
      (id : Bool -> Bool) =
        descend ∘ empiricalClass (experimentTrace intervene observe) := by
  dsimp
  apply (empirical_identifiability
    (experimentTrace (fun _ : Unit => id) (fun _ : Bool => ()))
    (id : Bool -> Bool)).2
  refine ⟨false, true, ?_, Bool.false_ne_true⟩
  intro actions
  induction actions with
  | nil => rfl
  | cons action remaining inductionHypothesis =>
      simpa only [experimentTrace, id_eq] using
        congrArg (List.cons ()) inductionHypothesis

#print axioms experimentTrace
#print axioms experimental_quotient_universality

end D5.S3.ConceptDynamics.Interventions.ExperimentalQuotientUniversality
