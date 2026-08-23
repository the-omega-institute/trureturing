/- GID: D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/AdmissionValidityPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admission-preserving transport pulls target validity back to the source. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-21):
   * Repository searches for validity preservation, admission-preserving maps,
     predicate pullback, and model satisfaction found no exact theorem.
   * `EffectiveImageNaturality` is adjacent transport machinery but concerns
     readout factorization on an image rather than validity of predicates.
   * Exact pinned-Mathlib hit `Set.MapsTo` expresses admission preservation and
     is used directly. No pinned theorem packages the target-validity transfer.
   * The `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- If every admissible target state satisfies a predicate and a transport
maps admissible source states to admissible target states, the pulled-back
predicate is valid on every admissible source state. -/
theorem validity_preserved_by_admission_map
    {X Y : Type*}
    (sourceAdmissible : X -> Prop)
    (targetAdmissible : Y -> Prop)
    (h : Concept X Y)
    (P : Y -> Prop)
    (targetValid : ∀ y, targetAdmissible y -> P y)
    (admissionPreserving :
      Set.MapsTo h {x | sourceAdmissible x} {y | targetAdmissible y}) :
    ∀ x, sourceAdmissible x -> (P ∘ h) x := by
  intro x sourceIsAdmissible
  exact targetValid (h x) (admissionPreserving sourceIsAdmissible)

/-- The transport carrier and both validity hypotheses have an inhabited
Boolean model. -/
example :
    let sourceAdmissible : Bool -> Prop := fun _ => True
    let targetAdmissible : Bool -> Prop := fun _ => True
    let h : Concept Bool Bool := id
    let P : Bool -> Prop := fun _ => True
    (∀ y, targetAdmissible y -> P y) ∧
      Set.MapsTo h {x | sourceAdmissible x} {y | targetAdmissible y} := by
  simp

/-- Target validity alone does not make its pullback valid when transport can
send an admissible source state outside the target admission domain. -/
example :
    let sourceAdmissible : Bool -> Prop := fun _ => True
    let targetAdmissible : Bool -> Prop := fun y => y = true
    let h : Concept Bool Bool := id
    let P : Bool -> Prop := fun y => y = true
    (∀ y, targetAdmissible y -> P y) ∧
      ¬(∀ x, sourceAdmissible x -> (P ∘ h) x) := by
  simp [Function.comp_apply]

/-- Admission preservation alone does not imply validity when the target
predicate itself is invalid. -/
example :
    let sourceAdmissible : Bool -> Prop := fun _ => True
    let targetAdmissible : Bool -> Prop := fun _ => True
    let h : Concept Bool Bool := id
    let P : Bool -> Prop := fun _ => False
    Set.MapsTo h {x | sourceAdmissible x} {y | targetAdmissible y} ∧
      ¬(∀ x, sourceAdmissible x -> (P ∘ h) x) := by
  simp [Function.comp_apply]

#print axioms validity_preserved_by_admission_map

end D5.S3.ConceptDynamics.Transport.AdmissionValidityPreservation
