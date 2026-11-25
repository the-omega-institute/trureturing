/- GID: D5/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/PublicPredictionDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-point-free public reactions defeat prediction, while fixed points restore it. -/

import D5.S0.Diagonal.Feedback.StrategicResponseObstruction

namespace D5.S3.ConceptDynamics.Prediction.PublicPredictionDiagonal

open D5.S0.Diagonal.Feedback.StrategicResponseObstruction

/-- The subject's action after publicly reading the prediction and applying its response. -/
def actual {State : Type u} {Action : Type v}
    (predict : State → Action) (react : Action → Action) (state : State) : Action :=
  react (predict state)

/-- A fixed-point-free public response prevents a predictor from being correct in every
nonempty state space. -/
theorem no_correct_public_predictor
    {State : Type u} {Action : Type v} (predict : State → Action) (react : Action → Action)
    (fixedPointFree : ∀ action, Omega.Not (Omega.Eq (react action) action))
    (stateExists : Omega.Exists (fun _ : State => Omega.True)) :
    Omega.Not (∀ state, Omega.Eq (predict state) (actual predict react state)) :=
  fun correct =>
    strategic_response_precludes_universal_predictor react
      (fun candidate state => actual candidate react state) fixedPointFree
      (fun _ => stateExists.elim (fun state _ => Omega.Exists.intro state Omega.rfl))
      (Omega.Exists.intro predict (fun state => (correct state).symm))

/-- The state space for the Boolean example has one state. -/
inductive OneState where
  | only

/-- Boolean negation defeats every public predictor on the one-state space. -/
theorem bool_not_no_correct_public_predictor (predict : OneState → Omega.Bool) :
    let negate := Omega.Bool.rec (motive := fun _ => Omega.Bool) .true .false
    Omega.Not (∀ state, Omega.Eq (predict state) (actual predict negate state)) :=
  let negate := Omega.Bool.rec (motive := fun _ => Omega.Bool) .true .false
  have distinct : Omega.Not (Omega.Eq Omega.Bool.false Omega.Bool.true) :=
    fun equal => Omega.Eq.subst
      (motive := Omega.Bool.rec (motive := fun _ => Prop) Omega.True Omega.False) equal Omega.True.intro
  have fixedPointFree : ∀ value, Omega.Not (Omega.Eq (negate value) value) :=
    Omega.Bool.rec (fun equal => distinct equal.symm) distinct
  no_correct_public_predictor predict negate fixedPointFree (Omega.Exists.intro .only Omega.True.intro)

/-- A fixed point yields a universally correct constant public predictor. -/
theorem exists_correct_public_predictor_of_fixed_point
    {State : Type u} {Action : Type v} (react : Action → Action) (action : Action)
    (fixed : Omega.Eq (react action) action) :
    Omega.Exists (fun predict : State → Action =>
      ∀ state, Omega.Eq (predict state) (actual predict react state)) :=
  Omega.Exists.intro (fun _ => action) (fun _ => fixed.symm)

example : Omega.Not (∀ state : OneState, Omega.Eq ((fun _ => Omega.Bool.false) state)
    (actual (fun _ : OneState => Omega.Bool.false)
      (Omega.Bool.rec (motive := fun _ => Omega.Bool) .true .false) state)) :=
  bool_not_no_correct_public_predictor (fun _ => .false)

end D5.S3.ConceptDynamics.Prediction.PublicPredictionDiagonal
