/- GID: D5/S3/ConceptDynamics/EmergencyEvidenceNecessity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EmergencyEvidenceNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evidence collisions force an authorization error and block necessity recovery. -/

import D5.S0.Rewriting.Quotients.InformedDisclosureDefect

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `informed_disclosure_defect` states the
     same-interface/different-target nonfactorization clause and is applied
     directly below.
   * Pinned Mathlib's `congrArg` transports evidence equality through every
     authorization rule; the repository hit already applies it to its clause.
   * Searches for emergency evidence, necessity authorization, false-positive,
     and false-negative packaging found no theorem containing both clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EmergencyEvidenceNecessity

open D5.S0.Rewriting.Quotients.InformedDisclosureDefect

/-- If equal evidence hides unequal Boolean necessity, every evidence-only
authorization rule either authorizes an unnecessary state or rejects a
necessary state, and necessity cannot factor through the evidence interface. -/
theorem emergency_evidence_necessity
    {State Evidence : Type*} (evidence : State → Evidence)
    (necessity : State → Bool) {x y : State}
    (hsame : evidence x = evidence y)
    (hdifferent : necessity x ≠ necessity y) :
    (∀ authorize : Evidence → Bool,
      (∃ state : State,
          necessity state = false ∧ authorize (evidence state) = true) ∨
        ∃ state : State,
          necessity state = true ∧ authorize (evidence state) = false) ∧
      ¬∃ recover : Evidence → Bool, necessity = recover ∘ evidence := by
  constructor
  · intro authorize
    have hnecessity :
        (necessity x = false ∧ necessity y = true) ∨
          (necessity y = false ∧ necessity x = true) := by
      cases hx : necessity x <;> cases hy : necessity y
      · exact False.elim (hdifferent (hx.trans hy.symm))
      · simp [hx, hy]
      · simp [hx, hy]
      · exact False.elim (hdifferent (hx.trans hy.symm))
    rcases hnecessity with hxy | hyx
    · cases hauthorize : authorize (evidence x)
      · right
        exact ⟨y, hxy.2, (congrArg authorize hsame).symm.trans hauthorize⟩
      · left
        exact ⟨x, hxy.1, hauthorize⟩
    · cases hauthorize : authorize (evidence x)
      · right
        exact ⟨x, hyx.2, hauthorize⟩
      · left
        exact ⟨y, hyx.1, (congrArg authorize hsame).symm.trans hauthorize⟩
  · exact (informed_disclosure_defect (Decision := Bool)
      evidence necessity hsame hdifferent).2

/-- Constant evidence on two states cannot recover their distinct necessities. -/
example :
    ¬∃ recover : Unit → Bool,
      (id : Bool → Bool) = recover ∘ (fun _ : Bool => ()) := by
  exact (emergency_evidence_necessity
    (fun _ : Bool => ()) id (x := false) (y := true)
    rfl Bool.false_ne_true).2

#print axioms emergency_evidence_necessity

end D5.S3.ConceptDynamics.EmergencyEvidenceNecessity
