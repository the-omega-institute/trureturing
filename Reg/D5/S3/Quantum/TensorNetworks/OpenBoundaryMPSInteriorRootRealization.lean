import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
import Reg.Support.DependentFamily

/-! Source reconstruction retains every original finite-boundary hypothesis.
The readout varies the actual raw-matrix equality relation. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix ComplexOrder
set_option autoImplicit false
noncomputable section

private def certificateSector : Sector := ⟨2, 0, 1⟩
private def certificateLeft : Fin 2 → ℂ := ![1, 2]
private def certificateRight : Fin 2 → ℂ := ![1, 0]

private lemma certificate_regular : Regular certificateSector := by
  norm_num [Regular, certificateSector, delta, alpha, beta, Complex.normSq_apply]

private lemma certificate_P : leftTarget certificateSector 1 certificateLeft 1 =
    !![13, 1; 1, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [leftTarget, Function.iterate_one, dualTransfer, core, B, G, certificateSector, certificateLeft,
      alpha, beta, Matrix.add_apply, mul_apply, Fin.sum_univ_two, conjTranspose_apply,
      vecMulVec_apply, Pi.star_apply, Matrix.diagonal_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue, Fin.reduceFinMk]
  all_goals norm_num [map_ofNat]

private lemma certificate_H : rightTarget certificateSector 1 certificateRight 1 =
    !![20, 4; 4, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rightTarget, Function.iterate_one, transfer, core, B, G, certificateSector, certificateRight,
      alpha, beta, Matrix.add_apply, mul_apply, Fin.sum_univ_two, conjTranspose_apply,
      vecMulVec_apply, Pi.star_apply, pow_two, Matrix.diagonal_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue, Fin.reduceFinMk]
  all_goals norm_num [map_ofNat]

private lemma certificate_invG : (G certificateSector (-1))⁻¹ =
    !![1/2, 1/2; -(1/2), 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [G, certificateSector, alpha, beta, Matrix.inv_def,
      Ring.inverse_eq_inv, adjugate_fin_two, det_fin_two]

private lemma certificate_invGsq : (G certificateSector (-1) ^ 2)⁻¹ =
    !![0, 1/2; -(1/2), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [G, certificateSector, alpha, beta, Matrix.inv_def,
      Ring.inverse_eq_inv, adjugate_fin_two, det_fin_two, pow_two,
      mul_apply, Fin.sum_univ_two]

private lemma certificate_left : (leftTarget certificateSector 1 certificateLeft 1).PosDef := by
  have hp : (leftTarget certificateSector 1 certificateLeft 1).PosSemidef := by
    rw [leftTarget, ← left_boundary_gram]
    exact posSemidef_conjTranspose_mul_self _
  apply hp.posDef_iff_det_ne_zero.mpr
  rw [certificate_P]
  norm_num [det_fin_two]

private lemma certificate_right : (rightTarget certificateSector 1 certificateRight 1).PosDef := by
  have hp : (rightTarget certificateSector 1 certificateRight 1).PosSemidef := by
    rw [rightTarget, ← tail_gram]
    exact (posSemidef_self_mul_conjTranspose _).mul_mul_conjTranspose_same _
  apply hp.posDef_iff_det_ne_zero.mpr
  rw [certificate_H]
  norm_num [det_fin_two]

private lemma certificate_left_root :
    (trialLeft certificateSector 1 (leftTarget certificateSector 1 certificateLeft 1) (-1)).det = 0 := by
  have he : trialLeft certificateSector 1
      (leftTarget certificateSector 1 certificateLeft 1) (-1) = !![4/5, 2; 2, 5] := by
    simp only [trialLeft, Function.iterate_one, inverseDualTransfer,
      certificate_invG, certificate_P]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [diagonalStarInverse, certificateSector, mul_apply, Fin.sum_univ_two,
        conjTranspose_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Fin.isValue, Fin.reduceFinMk]
    all_goals norm_num [map_ofNat]
  rw [he]
  norm_num [det_fin_two]

private lemma certificate_right_root :
    (trialRight certificateSector 1 (rightTarget certificateSector 1 certificateRight 1) (-1)).det = 0 := by
  have he : trialRight certificateSector 1
      (rightTarget certificateSector 1 certificateRight 1) (-1) = !![4/5, 6/5; 6/5, 9/5] := by
    simp only [trialRight, Function.iterate_one, inverseTransfer,
      certificate_invG, certificate_invGsq, certificate_H]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [diagonalInverse, certificateSector, mul_apply, Fin.sum_univ_two,
        conjTranspose_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Fin.isValue, Fin.reduceFinMk]
    all_goals norm_num [map_ofNat]
  rw [he]
  norm_num [det_fin_two]

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Matrix (Word 2) (Word 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Word 2) (Word 2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q → ∀ (s : Sector), Regular s →
    ∀ (z₀ : ℂ), z₀ ≠ 0 → ∀ (l r : Fin 2 → ℂ),
    (leftTarget s z₀ l p).PosDef → (rightTarget s z₀ r q).PosDef →
    ∀ (z : ℂ), z ≠ 0 → z ≠ z₀ →
    (trialLeft s p (leftTarget s z₀ l p) z).det = 0 →
    (trialRight s q (rightTarget s z₀ r q) z).det = 0 →
    ∃ φ : Word ((p + 2) + q) → ℂ,
      φ ∈ openBoundaryMPS ((p + 2) + q) ∧ φ ≠ 0 ∧
      R.readout () ⟨p, q⟩ (rawInterior p 2 q φ) (rawInterior p 2 q
        (mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r)) ∧
      ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ =
        η • mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨φ, _, _, hf, _⟩ := h 1 1 (by omega) (by omega) certificateSector
    certificate_regular 1 (by norm_num) certificateLeft certificateRight
    certificate_left certificate_right (-1) (by norm_num) (by norm_num)
    certificate_left_root certificate_right_root
  exact hf

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro he
  have hh : (1 : Matrix (Word 2) (Word 2) ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  have hv := congrFun (congrFun hh (fun _ => 0)) (fun _ => 0)
  norm_num at hv

def source_registration : Registration arena
    (type_of% @distinct_residual_root_actual_ambiguity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@distinct_residual_root_actual_ambiguity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@distinct_residual_root_actual_ambiguity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.distinct_residual_root_actual_ambiguity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

namespace IterateSmul
abbrev signature : Signature where
  Params := Unit
  State _ := Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bond
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (F : Bond → Bond),
    (∀ (t : ℂ) X, F (t • X) = t • F X) → ∀ (n : ℕ) (t : ℂ) (X : Bond),
    R.readout () () (F^[n] (t • X)) = t • F^[n] X
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun X : Bond => X 0 0)
    (h (fun X => X) (fun _ _ => rfl) 0 1 1)
  norm_num [rejected, realize] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrArg (fun X : Bond => X 0 0) he
  change (0 : ℂ) = 1 at hh
  norm_num at hh
def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.iterate_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.iterate_smul,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.iterate_smul)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.iterate_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.IterateSmul.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end IterateSmul

namespace TransferSmul
abbrev signature : Signature where
  Params := Unit
  State _ := Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bond
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Fin 2 → Bond) (t : ℂ) (X : Bond),
    R.readout () () (transfer A (t • X)) = t • transfer A X
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun X : Bond => X 0 0) (h (fun _ => 1) 1 1)
  norm_num [rejected, realize, transfer, Fin.sum_univ_two, Matrix.add_apply] at hh
  change (0 : ℂ) = 2 at hh
  norm_num at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrArg (fun X : Bond => X 0 0) he
  change (0 : ℂ) = 1 at hh
  norm_num at hh
def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.transfer_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.transfer_smul,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.transfer_smul)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.transfer_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.TransferSmul.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end TransferSmul
end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
