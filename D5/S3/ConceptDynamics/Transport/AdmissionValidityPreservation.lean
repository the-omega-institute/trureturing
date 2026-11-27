/- GID: D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/AdmissionValidityPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admission-preserving transport pulls target validity back to the source. -/

module
prelude
public import OmegaInit.Core

namespace D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation

open Omega

/-- Admission-preserving transport pulls target validity back to the source. -/
public theorem validity_preserved_by_admission_map
    {X : Type u} {Y : Type v}
    (sourceAdmissible : X → Prop) (targetAdmissible : Y → Prop)
    (transport : X → Y) (P : Y → Prop)
    (targetValid : ∀ y, targetAdmissible y → P y)
    (admissionPreserving : ∀ x, sourceAdmissible x → targetAdmissible (transport x)) :
    ∀ x, sourceAdmissible x → P (transport x) :=
  fun x admitted => targetValid (transport x) (admissionPreserving x admitted)

/-- The identity transport and constant true predicate satisfy both premises. -/
example :
    let admitted : Bool → Prop := fun _ => Omega.True
    let transport : Bool → Bool := fun x => x
    let P : Bool → Prop := fun _ => Omega.True
    Omega.And (∀ y, admitted y → P y) (∀ x, admitted x → admitted (transport x)) :=
  Omega.And.intro (fun _ h => h) (fun _ h => h)

/-- Target validity can hold while the unadmitted source image fails the predicate. -/
example :
    let sourceAdmissible : Bool → Prop := fun _ => Omega.True
    let targetAdmissible : Bool → Prop := fun y => Eq y .true
    let transport : Bool → Bool := fun x => x
    let P : Bool → Prop := fun y => Eq y .true
    Omega.And (∀ y, targetAdmissible y → P y)
      (Not (∀ x, sourceAdmissible x → P (transport x))) :=
  Omega.And.intro (fun _ h => h) (fun valid =>
    Eq.subst (motive := Bool.rec (motive := fun _ => Prop) Omega.True False)
      (valid .false Omega.True.intro) Omega.True.intro)

/-- Admission preservation can hold while the target predicate is false everywhere. -/
example :
    let admitted : Bool → Prop := fun _ => Omega.True
    let transport : Bool → Bool := fun x => x
    let P : Bool → Prop := fun _ => False
    Omega.And (∀ x, admitted x → admitted (transport x))
      (Not (∀ x, admitted x → P (transport x))) :=
  Omega.And.intro (fun _ h => h) (fun valid => valid .false Omega.True.intro)

end D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation
