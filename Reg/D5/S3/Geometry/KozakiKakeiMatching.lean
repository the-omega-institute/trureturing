import D5.S3.Geometry.KozakiKakeiMatching
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The signed matching evaluation is a readout on the full affine-coordinate family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Geometry.KozakiKakeiMatching

open _root_.D5.S3.Geometry.KozakiKakei
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit MvPolynomial
noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun m => Col m → ℂ) (fun _ => ℂ)

private def actual : Realization signature :=
  realize signature (fun _ m t => eval t (F m)) (fun e => nomatch e)

private def constant (z : ℂ) : Realization signature :=
  realize signature (fun _ _ _ => z) (fun e => nomatch e)

private def indices (i : Col 2) : ℂ := i.val

private theorem indices_injective : Function.Injective indices := by
  intro i j h
  apply Fin.ext
  change (i.val : ℂ) = (j.val : ℂ) at h
  exact_mod_cast h

private theorem evaluation_zero : eval (fun _ : Col 2 => (0 : ℂ)) (F 2) = 0 := by
  rw [eval_F]
  norm_num [evenProduct, oddProduct, minor_affine, Fin.prod_univ_two]

private theorem evaluation_indices : eval indices (F 2) = 2 := by
  norm_num [eval_F, evenProduct, oddProduct, minor_affine, Fin.prod_univ_two,
    evenVertex, oddVertex, indices]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, fun _ => 0, indices, ?_⟩
  change eval (fun _ : Col 2 => (0 : ℂ)) (F 2) ≠ eval indices (F 2)
  rw [evaluation_zero, evaluation_indices]
  norm_num

namespace Evaluation

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (t : Col m → ℂ),
    R.readout () m t = evenProduct (affine t) - oddProduct (affine t)

private theorem rejects_one : ¬ arena.Law (constant 1) := by
  intro h
  have bad := h (m := 2) (fun _ => 0)
  change (1 : ℂ) = evenProduct (affine (fun _ : Col 2 => (0 : ℂ))) -
    oddProduct (affine (fun _ : Col 2 => (0 : ℂ))) at bad
  rw [← eval_F, evaluation_zero] at bad
  exact one_ne_zero bad

def evidence : Registration arena (type_of% @eval_F) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_F, constant 1, rejects_one⟩
  sensitivity := sensitivity arena.Law actual (constant 1) rejects_one
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@eval_F) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.KozakiKakei.eval_F.__information_unit
  realizationName := `Reg.D5.S3.Geometry.KozakiKakeiMatching.Evaluation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m t => eval t (F m)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.KozakiKakeiMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Evaluation

namespace ConstantMatrices

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} {σ : Equiv.Perm (Col m)}, PreservesLevel σ →
    ∀ t : Col m → ℂ, Function.Injective t → R.readout () m t = 0 →
      eval t (rename σ (F m)) = 0

private theorem rejects_zero : ¬ arena.Law (constant 0) := by
  intro h
  have identity_preserves : PreservesLevel (Equiv.refl (Col 2)) := fun _ _ hz => hz
  have bad := h identity_preserves indices indices_injective rfl
  rw [eval_rename] at bad
  change eval indices (F 2) = 0 at bad
  rw [evaluation_indices] at bad
  norm_num at bad

def evidence : Registration arena (type_of% @constant_matrix_implication) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@constant_matrix_implication, constant 0, rejects_zero⟩
  sensitivity := sensitivity arena.Law actual (constant 0) rejects_zero
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@constant_matrix_implication) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.KozakiKakei.constant_matrix_implication.__information_unit
  realizationName := `Reg.D5.S3.Geometry.KozakiKakeiMatching.ConstantMatrices.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m t => eval t (F m)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.KozakiKakeiMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ConstantMatrices

end

end Reg.D5.S3.Geometry.KozakiKakeiMatching
