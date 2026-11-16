import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.SerreG2MatrixImage
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! The full field family and the actual Serre-to-matrix readout are retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.SerreG2MatrixImage

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuadraticForms.SerreG2MatrixImage
attribute [local instance 100] LieRing.ofAssociativeRing

universe u

structure Parameters where
  k : Type u
  field : Field k
  charZero : letI := field; CharZero k

attribute [instance] Parameters.field Parameters.charZero

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := LieAlgebra.g₂ p.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := matrixImage (k := p.k)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p x => serreMap (k := p.k) x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p, Function.Surjective (R.readout () p)

private def rational : Parameters.{u} := by
  refine ⟨ULift.{u} ℚ, inferInstance, ?_⟩
  constructor
  intro m n h
  exact Nat.cast_injective (show (m : ℚ) = (n : ℚ) from congrArg ULift.down h)

private theorem image_nontrivial (p : Parameters.{u}) :
    Nontrivial (matrixImage (k := p.k)) :=
  Module.nontrivial_of_finrank_pos (R := p.k) (by rw [matrixImage_finrank]; decide)

theorem exact_bridge :
    (type_of% (@_root_.D5.S3.QuadraticForms.SerreG2MatrixImage.serreMap_surjective.{u})) ↔
      arena.{u}.Law actual := by
  constructor
  · intro h p
    exact @h p.k p.field p.charZero
  · intro h k field charZero
    exact h ⟨k, field, charZero⟩

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p : Parameters.{u} := rational
  have : Nontrivial (matrixImage (k := p.k)) := image_nontrivial p
  obtain ⟨x, hx⟩ := exists_ne (0 : matrixImage (k := p.k))
  obtain ⟨y, hy⟩ := h p x
  exact hx hy.symm

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : Parameters.{u} := rational
  have : Nontrivial (matrixImage (k := p.k)) := image_nontrivial p
  obtain ⟨x, hx⟩ := exists_ne (0 : matrixImage (k := p.k))
  obtain ⟨y, hy⟩ := serreMap_surjective (k := p.k) x
  refine ⟨p, y, 0, ?_⟩
  change serreMap y ≠ serreMap (0 : LieAlgebra.g₂ p.k)
  simpa only [hy, map_zero] using hx

noncomputable def source_registration : Registration arena.{u}
    (type_of% (@_root_.D5.S3.QuadraticForms.SerreG2MatrixImage.serreMap_surjective.{u})) where
  actual := actual
  bridge := exact_bridge
  variation := ⟨exact_bridge.mp @_root_.D5.S3.QuadraticForms.SerreG2MatrixImage.serreMap_surjective,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuadraticForms.SerreG2MatrixImage.serreMap_surjective.{u})
      (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SerreG2MatrixImage.unit
  realizationName := `Reg.D5.S3.QuadraticForms.SerreG2MatrixImage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => serreMap (k := p.k) x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SerreG2MatrixImage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.QuadraticForms.SerreG2MatrixImage
