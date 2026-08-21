/- GID: D5/S3/ConceptDynamics/Audits/CorrectnessLegitimacySeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/CorrectnessLegitimacySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal correct results cannot determine opposite path legitimacy. -/

import D5.S3.ConceptDynamics.LegitimacyCorrectness

/- Library-search audit trail (2026-08-21):
   * Repository searches for correctness/result/legitimacy separation found no
     exact theorem. The imported `authorized_process_can_fail_factually` is the
     canonical family theorem for the converse independence direction.
   * `equal_content_does_not_determine_admission` is a concrete Boolean report
     countermodel, not the source's general path-predicate statement.
   * Pinned Mathlib's exact `congrArg` theorem transports a proposed result-only
     decision across the equal-result hypothesis and is applied directly below.
     `Function.FactorsThrough` and `Function.factorsThrough_iff` are adjacent
     hits, but neither includes correctness-restricted predicate agreement.
   * No exact pinned-Mathlib theorem packages the full contradiction. The
     `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.CorrectnessLegitimacySeparation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- If two correct paths have the same result and opposite legitimacy, no
predicate of the correct result alone can decide path legitimacy. -/
theorem correct_result_does_not_determine_legitimacy
    {Path Result : Type*}
    (result : Concept Path Result)
    (correct legitimate : Path -> Prop)
    {authorizedPath unauthorizedPath : Path}
    (sameResult : result authorizedPath = result unauthorizedPath)
    (authorizedCorrect : correct authorizedPath)
    (unauthorizedCorrect : correct unauthorizedPath)
    (authorizedLegitimate : legitimate authorizedPath)
    (unauthorizedIllegitimate : ¬ legitimate unauthorizedPath) :
    ¬ ∃ decide : Result -> Prop,
      ∀ path, correct path -> (decide (result path) ↔ legitimate path) := by
  rintro ⟨decide, agreesOnCorrectPaths⟩
  have authorizedDecision : decide (result authorizedPath) :=
    (agreesOnCorrectPaths authorizedPath authorizedCorrect).2
      authorizedLegitimate
  have sameDecision :
      decide (result authorizedPath) = decide (result unauthorizedPath) :=
    congrArg decide sameResult
  rw [sameDecision] at authorizedDecision
  exact unauthorizedIllegitimate
    ((agreesOnCorrectPaths unauthorizedPath unauthorizedCorrect).1
      authorizedDecision)

/-- The public hypotheses have a concrete pair of correct paths with equal
results and opposite legitimacy. -/
example :
    ¬ ∃ decide : Unit -> Prop,
      ∀ path : Bool, True -> (decide () ↔ path = true) := by
  exact correct_result_does_not_determine_legitimacy
    (result := fun _ => ())
    (correct := fun _ => True)
    (legitimate := fun path => path = true)
    (authorizedPath := true)
    (unauthorizedPath := false)
    rfl trivial trivial rfl Bool.false_ne_true

#print axioms correct_result_does_not_determine_legitimacy

end D5.S3.ConceptDynamics.Audits.CorrectnessLegitimacySeparation
