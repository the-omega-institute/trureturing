/- GID: D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-point-free public reactions defeat prediction, while fixed points restore it. -/

import D5.S0.Diagonal.Feedback.StrategicResponseObstruction

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'no_correct_public_predictor' D5 Golden/Frozen/accepted` found no match.
   * The requested fixed-point and diagonal search found the more general theorem
     `strategic_response_precludes_universal_predictor`, which is reused below.
   * Focused D5 prediction searches found no public-read definition or predictor-specific
     fixed-point converse, so the definition and both witnesses below are new content.
   * Pinned Mathlib defines `Function.IsFixedPt`; it is used instead of a local predicate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Prediction.PublicPredictionDiagonal

open D5.S0.Diagonal.Feedback.StrategicResponseObstruction

/-- The subject's action after publicly reading the prediction and applying its response.
This definition represents condition 1 through dependence on `predict state`, while the
response argument supplies condition 2. Condition 3 is the universal correctness claim
negated by `no_correct_public_predictor`. -/
def actual {State Action : Type*} (predict : State → Action) (react : Action → Action)
    (state : State) : Action :=
  react (predict state)

/-- A fixed-point-free public response prevents a predictor from being correct in every
nonempty state space. -/
theorem no_correct_public_predictor
    {State Action : Type*} (predict : State → Action) (react : Action → Action)
    (hfixed : ∀ action, ¬ Function.IsFixedPt react action)
    (stateExists : Nonempty State) :
    ¬ ∀ state, predict state = actual predict react state := by
  intro hcorrect
  rcases stateExists with ⟨state⟩
  have hnoCorrectResponse :
      ¬ ∃ candidate : State → Action, ∀ s,
        actual candidate react s = candidate s := by
    apply strategic_response_precludes_universal_predictor react
      (fun candidate s => actual candidate react s) hfixed
    intro candidate
    exact ⟨state, rfl⟩
  exact hnoCorrectResponse ⟨predict, fun s => (hcorrect s).symm⟩

/-- Boolean negation is a concrete fixed-point-free response, so it defeats every public
predictor on the one-state space. -/
theorem bool_not_no_correct_public_predictor (predict : Unit → Bool) :
    ¬ ∀ state, predict state = actual predict Bool.not state := by
  exact no_correct_public_predictor predict Bool.not (by decide) ⟨()⟩

/-- The no-fixed-point condition is essential: a fixed point yields a universally correct
constant public predictor. -/
theorem exists_correct_public_predictor_of_fixed_point
    {State Action : Type*} (react : Action → Action) (action : Action)
    (hfixed : Function.IsFixedPt react action) :
    ∃ predict : State → Action, ∀ state, predict state = actual predict react state := by
  refine ⟨fun _ => action, ?_⟩
  intro state
  exact hfixed.symm

example :
    ¬ ∀ state : Unit, (fun _ => false) state =
      actual (fun _ : Unit => false) Bool.not state :=
  bool_not_no_correct_public_predictor (fun _ => false)

#print axioms no_correct_public_predictor

end D5.S3.ConceptDynamics.Prediction.PublicPredictionDiagonal
