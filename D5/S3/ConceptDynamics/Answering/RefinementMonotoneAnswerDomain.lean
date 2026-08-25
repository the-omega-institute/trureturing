/- GID: D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical safe answering expands monotonically under concept refinement. -/

import D5.S3.ConceptDynamics.Answering.SafeAnswerCoverageMaximality
import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'refinement_monotone_answer_domain' D5 Golden/Frozen/accepted`
     found no existing declaration or accepted duplicate.
   * The required `answer|Answering|refinement.*monotone` search under
     `D5/S3/ConceptDynamics` found the 454.2 safe-answer module and related refinement
     theorems, but no theorem combining canonical answering with refinement.
   * Exact repository hits `ConceptJoinUniversal.Refines`, `canonicalSafeAnswer`,
     `canonical_safe_answer_zero_error`, and `safe_answer_coverage_maximality` provide
     the factorization relation and all answerer machinery reused below.
   * Pinned Mathlib provides `Set.ssubset_iff_of_subset` for the strict finite smoke
     test; the proofs otherwise use function equality and existential elimination.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.RefinementMonotoneAnswerDomain

open D5.S3.ConceptDynamics.Answering.SafeAnswerCoverageMaximality
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Admitted states on which the canonical safe answerer returns a target value. -/
def answerDomain {X B Y : Type*} (A : X -> Prop) (q : Concept X B) (T : X -> Y) :
    Set X :=
  {x | A x ∧ ∃ y, canonicalSafeAnswer A q T (q x) = some y}

/-- Refining a concept preserves every canonical answer, including its target value. -/
theorem refinement_monotone_answer_domain
    {X C D Y : Type*} (A : X -> Prop) (q_C : Concept X C) (q_D : Concept X D)
    (T : X -> Y) (refinement : Refines q_C q_D) (x : X) (hx : A x) (y : Y)
    (hAnswer : canonicalSafeAnswer A q_C T (q_C x) = some y) :
    canonicalSafeAnswer A q_D T (q_D x) = some y := by
  rcases refinement with ⟨factor, hfactor⟩
  apply safe_answer_coverage_maximality
    (g := fun d => canonicalSafeAnswer A q_C T (factor d))
  · intro state hState target hPulledBackAnswer
    apply canonical_safe_answer_zero_error A q_C T state hState target
    rw [hfactor] at hPulledBackAnswer ⊢
    unfold Function.comp at hPulledBackAnswer ⊢
    exact hPulledBackAnswer
  · exact ⟨x, hx, rfl⟩
  · rw [hfactor] at hAnswer ⊢
    unfold Function.comp at hAnswer ⊢
    exact hAnswer

/-- The admitted safe-answer domain of a coarse concept is contained in that of any
refinement. -/
theorem answer_domain_monotone
    {X C D Y : Type*} (A : X -> Prop) (q_C : Concept X C) (q_D : Concept X D)
    (T : X -> Y) (refinement : Refines q_C q_D) :
    answerDomain A q_C T ⊆ answerDomain A q_D T := by
  intro x hx
  change A x ∧ ∃ y, canonicalSafeAnswer A q_C T (q_C x) = some y at hx
  change A x ∧ ∃ y, canonicalSafeAnswer A q_D T (q_D x) = some y
  rcases hx with ⟨hAdmitted, y, hAnswer⟩
  exact ⟨hAdmitted, y,
    refinement_monotone_answer_domain A q_C q_D T refinement x hAdmitted y hAnswer⟩

/-- Splitting a two-state constant fiber by identity strictly enlarges the answer domain. -/
example :
    answerDomain (fun _ : Bool => True) (fun _ => ()) (id : Bool -> Bool) ⊂
      answerDomain (fun _ : Bool => True) (id : Bool -> Bool) (id : Bool -> Bool) := by
  refine (Set.ssubset_iff_of_subset ?_).2 ?_
  · apply answer_domain_monotone
    exact ⟨fun _ : Bool => (), rfl⟩
  · refine ⟨false, ?_, ?_⟩
    · refine ⟨trivial, false, ?_⟩
      apply safe_answer_coverage_maximality (g := fun b : Bool => some b)
      · intro _ _ y hAnswer
        exact Option.some.inj hAnswer
      · exact ⟨false, trivial, rfl⟩
      · rfl
    · rintro ⟨_, y, hAnswer⟩
      have hNone :
          canonicalSafeAnswer (fun _ : Bool => True) (fun _ => ())
            (id : Bool -> Bool) () = none := by
        unfold canonicalSafeAnswer
        split
        · rename_i hUnique
          exfalso
          apply Bool.false_ne_true
          apply hUnique.unique
          · exact ⟨false, trivial, rfl, rfl⟩
          · exact ⟨true, trivial, rfl, rfl⟩
        · rfl
      rw [hNone] at hAnswer
      contradiction

#print axioms refinement_monotone_answer_domain

end D5.S3.ConceptDynamics.Answering.RefinementMonotoneAnswerDomain
