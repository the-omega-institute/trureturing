/- GID: D5/S3/ConceptDynamics/Communication/PropositionLeakLowerBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/PropositionLeakLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A transcript deciding a nonconstant proposition must reveal a distinction. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/- Library-search audit trail (2026-08-23):
   * `grep -A2 '^  Disclosure:' Meta/domains.yaml` returned no hit, so this
     module uses the controlled `ConceptDynamics/Communication` route.
   * `rg -n -F 'transcript_leaks_at_least_the_proposition' D5
     Golden/Frozen/accepted` returned no hit.
   * Searches for `transcript|disclosure|leak|zero.?knowledge` found
     `InformedDisclosureDefect`, `ExactTargetForcedLeak`, and
     `SubthresholdCoalitionLearnsNothing`; none states the nonconstant-Boolean
     transcript conclusion or constructs an exact-proposition transcript.
   * `TargetRecoveryCriterion.target_recovery_criterion` packages the general
     recovery criterion but not the nontrivial lower bound or exact witness.
   * `AnswerabilityCriterion.answerability_criterion` is the exact reusable
     factorization-to-fiber-constancy result and is applied below. The local work
     adds nontriviality, extracts a transcript distinction, defines equality of
     transcript and proposition fibers, and constructs the proposition-only witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.PropositionLeakLowerBound

/-- A transcript proves a proposition when a deterministic decoder recovers its
Boolean truth value from the transcript alone. -/
def ProvesProposition {Secret Transcript : Type*}
    (transcript : Secret → Transcript) (Q : Secret → Bool) : Prop :=
  ∃ decide : Transcript → Bool, Q = decide ∘ transcript

/-- A transcript leaks exactly a proposition when it identifies precisely the
pairs of secret states that the proposition identifies. -/
def LeaksExactlyProposition {Secret Transcript : Type*}
    (transcript : Secret → Transcript) (Q : Secret → Bool) : Prop :=
  ∀ x y, transcript x = transcript y ↔ Q x = Q y

/-- Any transcript proving a nonconstant secret proposition distinguishes at
least one pair of states separated by that proposition. In particular, a
constant transcript cannot prove a nontrivial proposition. -/
theorem transcript_leaks_at_least_the_proposition
    {Secret Transcript : Type*} (transcript : Secret → Transcript)
    (Q : Secret → Bool) (proves : ProvesProposition transcript Q)
    (nontrivial : ∃ s₁ s₂, Q s₁ ≠ Q s₂) :
    ∃ s₁ s₂, transcript s₁ ≠ transcript s₂ := by
  obtain ⟨s₁, s₂, different⟩ := nontrivial
  refine ⟨s₁, s₂, ?_⟩
  intro sameTranscript
  apply different
  exact
    (D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      s₁ transcript Q).1.mp proves sameTranscript

/-- The proposition itself is a transcript whose indistinguishability relation
is exactly the proposition's relation and which proves the proposition. -/
theorem proposition_only_transcript_exists {Secret : Type*} (Q : Secret → Bool) :
    ∃ transcript : Secret → Bool,
      LeaksExactlyProposition transcript Q ∧ ProvesProposition transcript Q := by
  refine ⟨Q, ?_, ?_⟩
  · intro x y
    rfl
  · refine ⟨id, ?_⟩
    funext x
    rfl

/-- The identity Boolean proposition gives a concrete nontrivial smoke test. -/
example :
    ProvesProposition (id : Bool → Bool) id ∧
      LeaksExactlyProposition (id : Bool → Bool) id ∧
      ∃ s₁ s₂, (id : Bool → Bool) s₁ ≠ id s₂ := by
  have proves : ProvesProposition (id : Bool → Bool) id := by
    refine ⟨id, ?_⟩
    funext x
    rfl
  have exactLeak : LeaksExactlyProposition (id : Bool → Bool) id := by
    intro x y
    rfl
  refine ⟨proves, exactLeak, ?_⟩
  exact transcript_leaks_at_least_the_proposition (id : Bool → Bool) id proves
    ⟨false, true, Bool.false_ne_true⟩

#print axioms transcript_leaks_at_least_the_proposition

end D5.S3.ConceptDynamics.Communication.PropositionLeakLowerBound
