/- GID: D5/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TransportValidity/OldLanguageValidityConservativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admitted-state surjective pullback preserves and reflects old validity. -/

module
prelude
public import D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation

namespace D5.S3.ConceptDynamics.TransportValidity.OldLanguageValidityConservativity

open Omega
open D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation

/-- A projection that preserves admission and surjects onto admitted old states
preserves and reflects predicate validity. -/
public theorem old_language_validity_conservative
    {X : Type u} {Extension : Type v}
    (oldAdmissible : X → Prop) (extensionAdmissible : Extension → Prop)
    (project : Extension → X)
    (admissionPreserving : ∀ extended, extensionAdmissible extended →
      oldAdmissible (project extended))
    (admissionSurjective : ∀ x, oldAdmissible x →
      Omega.Exists (fun extended => Omega.And (extensionAdmissible extended) (Eq (project extended) x)))
    (P : X → Prop) :
    Omega.Iff (∀ x, oldAdmissible x → P x) (∀ extended, extensionAdmissible extended → P (project extended)) :=
  Omega.Iff.intro
    (fun oldValid => validity_preserved_by_admission_map
      extensionAdmissible oldAdmissible project P oldValid admissionPreserving)
    (fun extensionValid x oldAdmission =>
      (admissionSurjective x oldAdmission).elim (fun extended evidence =>
        Eq.subst (motive := P) evidence.right (extensionValid extended evidence.left)))

end D5.S3.ConceptDynamics.TransportValidity.OldLanguageValidityConservativity
