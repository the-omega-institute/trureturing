/- GID: D5/S3/ConceptDynamics/DecisionValue/DecisionWithoutFullPrediction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/DecisionWithoutFullPrediction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One constant concept determines every optimal action without determining full payoffs. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-22):
   * Repository searches for decision sufficiency, optimal-action/full-prediction
     separation, the source theorem number, and the atom id found no exact theorem.
   * Exact family hits `ConceptFiberDecomposition.Concept` and
     `ConceptJoinUniversal.Refines` are imported and used directly; no sibling
     readout carrier or refinement relation is declared here.
   * `BlindNaturalityCountermodel.blind_naturality_counterexample` is an adjacent
     constant-readout nonfactorization pattern, but it has no payoff or optimal-action
     construction and therefore is not an exact result.
   * Pinned Mathlib supplies `List.argmax` and generic `IsGreatest` machinery, but no
     result packages this source countermodel. The Boolean maximality predicate below
     directly represents the source argmax correspondence without list encoding.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.DecisionWithoutFullPrediction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- The source payoff table. `true` is action a, `false` is action b; the two
states are represented by `false` and `true`. -/
def decisionPayoff : Bool -> Bool -> Real
  | false, false => 0
  | false, true => 10
  | true, false => 1
  | true, true => 100

/-- The target concept whose value is the set of payoff-maximizing actions. -/
def optimalActions : Concept Bool (Set Bool) :=
  fun state => {action | forall alternative,
    decisionPayoff state alternative <= decisionPayoff state action}

/-- The complete-result target records the payoff of every action at a state. -/
def fullPayoffProfile : Concept Bool (Bool -> Real) :=
  fun state action => decisionPayoff state action

/-- The concept that makes no distinction between the two source states. -/
def constantConcept : Concept Bool Unit := fun _ => ()

/-- The constant concept determines the maximizing action set in both states,
but it cannot determine their distinct complete payoff profiles. -/
theorem decision_sufficiency_without_full_prediction :
    Refines optimalActions constantConcept /\
      Not (Refines fullPayoffProfile constantConcept) := by
  constructor
  · refine ⟨fun _ => ({true} : Set Bool), ?_⟩
    unfold Function.comp
    funext state
    apply Set.ext
    intro action
    cases state <;> cases action <;>
      simp [optimalActions, decisionPayoff, Function.comp_def]
  · rintro ⟨factor, hfactor⟩
    have hstates : fullPayoffProfile false = fullPayoffProfile true := by
      unfold Function.comp at hfactor
      calc
        fullPayoffProfile false = factor () := by
          simpa [constantConcept] using congrFun hfactor false
        _ = fullPayoffProfile true := by
          simpa [constantConcept] using (congrFun hfactor true).symm
    have haPayoff := congrFun hstates true
    norm_num [fullPayoffProfile, decisionPayoff] at haPayoff

/-- The source construction computes action a as the unique optimizer in each state. -/
example : optimalActions false = {true} /\ optimalActions true = {true} := by
  constructor <;> apply Set.ext <;> intro action <;> cases action <;>
    simp [optimalActions, decisionPayoff]

#print axioms decision_sufficiency_without_full_prediction

end D5.S3.ConceptDynamics.DecisionValue.DecisionWithoutFullPrediction
