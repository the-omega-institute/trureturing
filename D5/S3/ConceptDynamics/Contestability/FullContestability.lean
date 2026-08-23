/- GID: D5/S3/ConceptDynamics/Contestability/FullContestability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Contestability/FullContestability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete contestability selects accepted challenges that support correct review. -/

import D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'full_contestability_yields_correct_review' D5 Golden/Frozen/accepted`
     returned no matches before this module was added.
   * Searching `FullyContestable|full.?contestab|Applicable` in those locations
     found no existing formalization of the three-part challenge condition.
   * Searching `challenge_blind_review_cannot_separate` and
     `correct_challenge_blind_review_exists_iff_coverage` found the upstream
     `InvisibleDefectUnrepairable` module and one unrelated downstream use.
   * `rg -n 'axiom choice|theorem.*choice|choose_spec' .lake/packages/mathlib/Mathlib`
     found generic choice uses but no matching state-indexed selector theorem, so
     the pointwise witnesses here are selected with core `Classical.choose`.
   * The main proof reuses the positive direction of the upstream coverage iff
     after choosing an accepted challenge for every erroneous state. The negative
     comparison directly reuses the upstream challenge-blind obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Contestability.FullContestability

open D5.S3.ConceptDynamics.Contestability.InvisibleDefectUnrepairable

/-- Complete contestability supplies every erroneous state with an applicable,
institutionally valid challenge whose judgment is the target outcome. -/
def FullyContestable {State Challenge Outcome : Type*}
    (Erroneous : State -> Prop) (Applicable Valid : State -> Challenge -> Prop)
    (judgment : Challenge -> State -> Outcome) (target : State -> Outcome) : Prop :=
  forall x, Erroneous x ->
    Exists fun w => Applicable x w /\ Valid x w /\ judgment w x = target x

/-- The subtype on which a review mechanism is required to repair outcomes. -/
def ErrorState (State : Type*) (Erroneous : State -> Prop) :=
  {x : State // Erroneous x}

/-- Asking the selected challenge exposes its judgment as the reviewer's observation. -/
def selectedChallengeAnswer
    {State Challenge Outcome : Type*} {Erroneous : State -> Prop}
    (judgment : Challenge -> State -> Outcome)
    (selected : ErrorState State Erroneous -> Challenge) :
    Unit -> ErrorState State Erroneous -> Outcome :=
  fun _ x => judgment (selected x) x.1

/-- At a state, the review output is produced by some applicable and valid challenge. -/
def UsesAcceptedChallengeAt
    {State Challenge Outcome : Type*}
    (Applicable Valid : State -> Challenge -> Prop)
    (judgment : Challenge -> State -> Outcome) (review : State -> Outcome)
    (x : State) : Prop :=
  Exists fun w => Applicable x w /\ Valid x w /\ review x = judgment w x

/-- Complete contestability yields selected accepted challenges and a challenge-blind
review mechanism that returns the target on every erroneous state. -/
theorem full_contestability_yields_correct_review
    {State Challenge Outcome : Type*}
    (Erroneous : State -> Prop) (Applicable Valid : State -> Challenge -> Prop)
    (judgment : Challenge -> State -> Outcome) (target : State -> Outcome)
    (hFull : FullyContestable Erroneous Applicable Valid judgment target) :
    Exists fun selected : ErrorState State Erroneous -> Challenge =>
      (forall x, Applicable x.1 (selected x) /\ Valid x.1 (selected x) /\
        judgment (selected x) x.1 = target x.1) /\
      Exists fun review : ErrorState State Erroneous -> Outcome =>
        ChallengeBlind (selectedChallengeAnswer judgment selected) review /\
          forall x, review x = target x.1 := by
  let selected : ErrorState State Erroneous -> Challenge :=
    fun x => Classical.choose (hFull x.1 x.2)
  have hSelected (x : ErrorState State Erroneous) :
      Applicable x.1 (selected x) /\ Valid x.1 (selected x) /\
        judgment (selected x) x.1 = target x.1 :=
    Classical.choose_spec (hFull x.1 x.2)
  refine ⟨selected, hSelected, ?_⟩
  apply (correct_challenge_blind_review_exists_iff_coverage
    (selectedChallengeAnswer judgment selected) (fun x => target x.1)).2
  intro s t sameAnswers
  calc
    target s.1 = judgment (selected s) s.1 := (hSelected s).2.2.symm
    _ = judgment (selected t) t.1 := sameAnswers ()
    _ = target t.1 := (hSelected t).2.2

/-- If an erroneous state has no accepted correct challenge, challenge-based review fails there.
If it is also indistinguishable from a state with another target, global blind review fails. -/
theorem absent_challenge_and_blindness_prevent_review
    {State Challenge Outcome : Type*}
    (Erroneous : State -> Prop) (Applicable Valid : State -> Challenge -> Prop)
    (judgment : Challenge -> State -> Outcome) (target : State -> Outcome)
    (x y : State) (hx : Erroneous x)
    (noChallenge : forall w, Not (Applicable x w /\ Valid x w /\
      judgment w x = target x))
    (sameAnswers : forall w, judgment w x = judgment w y)
    (differentTargets : target x ≠ target y) :
    Not (FullyContestable Erroneous Applicable Valid judgment target) /\
      (forall review, UsesAcceptedChallengeAt Applicable Valid judgment review x ->
        review x ≠ target x) /\
      Not (Exists fun review : State -> Outcome =>
        ChallengeBlind judgment review /\ forall s, review s = target s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hFull
    rcases hFull x hx with ⟨w, hw⟩
    exact noChallenge w hw
  · intro review hUses hCorrect
    rcases hUses with ⟨w, hApplicable, hValid, hReview⟩
    apply noChallenge w
    refine ⟨hApplicable, hValid, ?_⟩
    calc
      judgment w x = review x := hReview.symm
      _ = target x := hCorrect
  · exact challenge_blind_review_cannot_separate
      judgment target x y sameAnswers differentTargets

/-- Boolean identity repair is a nonvacuous completely contestable instance: both
states are erroneous, and each state itself is an accepted challenge. -/
theorem bool_identity_is_nontrivially_fully_contestable :
    (Exists fun _ : Bool => True) /\
      FullyContestable (fun _ : Bool => True) (fun x w => w = x)
        (fun _ _ : Bool => True) (fun w _ : Bool => w) (fun x => x) := by
  constructor
  · exact ⟨false, trivial⟩
  · intro x _
    exact ⟨x, rfl, trivial, rfl⟩

example :
    FullyContestable (fun _ : Bool => True) (fun x w => w = x)
      (fun _ _ : Bool => True) (fun w _ : Bool => w) (fun x => x) := by
  exact bool_identity_is_nontrivially_fully_contestable.2

#print axioms full_contestability_yields_correct_review

end D5.S3.ConceptDynamics.Contestability.FullContestability
