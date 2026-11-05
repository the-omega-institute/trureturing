import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ q =>
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ q : ℕ, 7 ≤ q → R.readout () () q < 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 7 (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hh

private theorem first_readout_pos :
    0 < twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 := by
  rw [first_coefficient_eq 1]
  simp only [pow_one]
  have hr :
      (45 * Real.pi / 16) * (1 / 2 : ℝ) -
          4 * (16 / (9 * Real.pi)) - 6 * (16 / (15 * Real.pi)) =
        (2025 * Real.pi ^ 2 - 19456) / (1440 * Real.pi) := by
    field_simp [ne_of_gt Real.pi_pos]
    <;> ring
  rw [hr]
  apply div_pos
  · nlinarith [Real.pi_gt_d2, sq_nonneg (Real.pi - 3.14)]
  · positivity

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 7, ?_⟩
  change twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 ≠
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 7 => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1
  exact ne_of_gt ((half_parameter_family_neg 7 (by norm_num)).trans first_readout_pos)

def family : Registration arena (type_of% @half_parameter_family_neg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨half_parameter_family_neg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_parameter_family_neg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.Negative.unit
  realizationName := `Reg.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q =>
    twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
