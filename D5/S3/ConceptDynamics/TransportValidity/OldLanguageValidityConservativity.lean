/- GID: D5/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admitted-state surjective pullback preserves and reflects old validity. -/

import D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation

/- Library-search audit trail (2026-08-25):
   * `AdmissionValidityPreservation.validity_preserved_by_admission_map` is the
     exact source §427 preservation half and is applied below.
   * `ConservativeExtensionAnswerability` proves a different equivalence for
     `Refines`, not validity of old predicates on admitted states.
   * Searches for old-language validity conservativity, admitted-domain
     reflection, and a `P ∘ p` validity equivalence found no exact D5 theorem.
   * Pinned Mathlib supplies generic surjection and function-composition facts,
     but no exact admitted-model validity equivalence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TransportValidity.OldLanguageValidityConservativity

open D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation

/-- A projection that preserves admission and is surjective on admitted old
states makes every old predicate valid exactly when its pullback is valid in the
extension. -/
theorem old_language_validity_conservative
    {X X' : Type*}
    (oldAdmissible : X → Prop)
    (extensionAdmissible : X' → Prop)
    (p : X' → X)
    (admissionPreserving :
      Set.MapsTo p {x' | extensionAdmissible x'} {x | oldAdmissible x})
    (admissionSurjective :
      ∀ x, oldAdmissible x →
        ∃ x', extensionAdmissible x' ∧ p x' = x)
    (P : X → Prop) :
    (∀ x, oldAdmissible x → P x) ↔
      ∀ x', extensionAdmissible x' → (P ∘ p) x' := by
  constructor
  · intro oldValid
    exact validity_preserved_by_admission_map
      extensionAdmissible oldAdmissible p P oldValid admissionPreserving
  · intro extensionValid x oldAdmission
    obtain ⟨x', extensionAdmission, projected⟩ :=
      admissionSurjective x oldAdmission
    rw [← projected]
    exact extensionValid x' extensionAdmission

#print axioms old_language_validity_conservative

end D5.S3.ConceptDynamics.TransportValidity.OldLanguageValidityConservativity
