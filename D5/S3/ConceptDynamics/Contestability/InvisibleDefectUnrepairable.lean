/- GID: D5/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Contestability/InvisibleDefectUnrepairable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Challenge-indistinguishable states with different targets defeat every blind review. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'challenge_blind_review_cannot_separate' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested `Indistinguish|indistinguishable` search found seven unrelated
     families. `ActionExpansionIndistinguishability` only proves monotonicity under
     action-set expansion and supplies no challenge-to-reviewer obstruction.
   * The requested `contest|challenge|review` search found
     `ExplainableNotContestable`; its finite case/appeal witness is not this general
     arbitrary-state impossibility theorem.
   * `MixedFiberZeroErrorImpossible` is restricted to Bool labels, while
     `TargetRecoveryCriterion` concerns factorization through one readout. Neither
     directly matches a state reviewer constrained only by challenge answers.
   * No reusable exact theorem was found. The proofs below use only equality
     transport, function application congruence, and Boolean constructor inequality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable

/-- A reviewer is challenge-blind when challenge-indistinguishable states always
receive the same reviewed outcome. -/
def ChallengeBlind {State Challenge Response Outcome : Type*}
    (ask : Challenge -> State -> Response) (review : State -> Outcome) : Prop :=
  ∀ s t, (∀ c, ask c s = ask c t) -> review s = review t

/-- If two states answer every acceptable challenge identically but require different
outcomes, no challenge-blind reviewer can be correct on every state. -/
theorem challenge_blind_review_cannot_separate
    {State Challenge Response Outcome : Type*}
    (ask : Challenge -> State -> Response) (required : State -> Outcome)
    (x y : State) (sameAnswers : ∀ c, ask c x = ask c y)
    (differentRequirements : required x ≠ required y) :
    ¬(∃ review : State -> Outcome,
      ChallengeBlind ask review ∧ ∀ s, review s = required s) := by
  rintro ⟨review, challengeBlind, correct⟩
  apply differentRequirements
  calc
    required x = review x := (correct x).symm
    _ = review y := challengeBlind x y sameAnswers
    _ = required y := correct y

/-- A fully correct challenge-blind reviewer exists exactly when challenge answers
separate every pair of states whose required outcomes differ. -/
theorem correct_challenge_blind_review_exists_iff_coverage
    {State Challenge Response Outcome : Type*}
    (ask : Challenge -> State -> Response) (required : State -> Outcome) :
    (∃ review : State -> Outcome,
      ChallengeBlind ask review ∧ ∀ s, review s = required s) ↔
      ∀ s t, (∀ c, ask c s = ask c t) -> required s = required t := by
  constructor
  · rintro ⟨review, challengeBlind, correct⟩ s t sameAnswers
    calc
      required s = review s := (correct s).symm
      _ = review t := challengeBlind s t sameAnswers
      _ = required t := correct t
  · intro coverage
    exact ⟨required, coverage, fun _ => rfl⟩

/-- A constant Unit-valued challenge cannot distinguish the two Boolean states,
although the identity target requires different outcomes on them. -/
theorem constant_unit_challenge_is_blind_to_bool_defect :
    (∀ c : Unit, (fun (_ : Unit) (_ : Bool) => ()) c false =
      (fun (_ : Unit) (_ : Bool) => ()) c true) ∧
    (id : Bool -> Bool) false ≠ (id : Bool -> Bool) true := by
  constructor
  · intro c
    rfl
  · exact Bool.false_ne_true

/-- Consequently, no reviewer using only the constant Unit challenge can correctly
implement the Boolean identity target. -/
theorem constant_unit_challenge_cannot_review_bool :
    ¬(∃ review : Bool -> Bool,
      ChallengeBlind (fun (_ : Unit) (_ : Bool) => ()) review ∧
        ∀ state, review state = (id : Bool -> Bool) state) := by
  rcases constant_unit_challenge_is_blind_to_bool_defect with
    ⟨sameAnswers, differentRequirements⟩
  exact challenge_blind_review_cannot_separate
    (fun _ : Unit => fun _ : Bool => ()) (id : Bool -> Bool) false true
    sameAnswers differentRequirements

example :
    ¬(∃ review : Bool -> Bool,
      ChallengeBlind (fun (_ : Unit) (_ : Bool) => ()) review ∧
        ∀ state, review state = (id : Bool -> Bool) state) :=
  constant_unit_challenge_cannot_review_bool

#print axioms challenge_blind_review_cannot_separate

end D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable
