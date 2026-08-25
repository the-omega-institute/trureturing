/- GID: D5/S3/ConceptDynamics/TransportValidity/AdmittedValidityReflection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TransportValidity/AdmittedValidityReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Surjectivity on admitted states reflects validity of pulled-back predicates. -/

import D5.S3.ConceptDynamics.TransportValidity.OldLanguageValidityConservativity

/- Library-search audit trail (2026-08-25):
   * `OldLanguageValidityConservativity` is a nearby stronger iff that also
     assumes admission preservation; it is imported for the family semantics
     but cannot be applied without adding a premise absent from the source.
   * Repository searches for admitted-domain validity reflection found no
     exact one-way theorem with only surjectivity and pullback validity.
   * Pinned Mathlib supplies generic function and existential reasoning, but no
     exact predicate-validity theorem on restricted admission domains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TransportValidity.AdmittedValidityReflection

/-- A predicate valid after pullback along a map surjective on the admission
domain is valid on every admitted target state. -/
theorem validity_reflected_by_admitted_surjection
    {X Y : Type*}
    (sourceAdmissible : X -> Prop)
    (targetAdmissible : Y -> Prop)
    (h : X -> Y)
    (P : Y -> Prop)
    (admissionSurjective : forall y, targetAdmissible y ->
      exists x, sourceAdmissible x ∧ h x = y)
    (sourceValid : forall x, sourceAdmissible x -> (P ∘ h) x) :
    forall y, targetAdmissible y -> P y := by
  intro y targetAdmission
  obtain ⟨x, sourceAdmission, projected⟩ :=
    admissionSurjective y targetAdmission
  rw [← projected]
  exact sourceValid x sourceAdmission

#print axioms validity_reflected_by_admitted_surjection

end D5.S3.ConceptDynamics.TransportValidity.AdmittedValidityReflection
