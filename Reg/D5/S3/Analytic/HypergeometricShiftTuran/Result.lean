import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.HypergeometricShiftTuran.Result
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.HypergeometricShiftTuran.Defs
open _root_.D5.S3.Analytic.HypergeometricShiftTuran.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.HypergeometricShiftTuran.Result

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ q =>
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ q : ℕ, 6 ≤ q → R.readout () () q < 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 6 (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 6, ?_⟩
  change turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 ≠
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 6 => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1
  have hz : turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1 = 0 := by
    norm_num [turanCoeff, coeff, Finset.sum_range_succ]
  rw [hz]
  exact ne_of_gt (half_parameter_family_neg 6 (by norm_num))

def family : Registration arena (type_of% @half_parameter_family_neg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨half_parameter_family_neg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@half_parameter_family_neg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.HypergeometricShiftTuran.Result.Negative.unit
  realizationName := `Reg.D5.S3.Analytic.HypergeometricShiftTuran.Result.family
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
    turanCoeff (fun _ : Fin 0 => 0) (fun _ : Fin q => (1 / 2 : ℝ))
      1 (1 / 2) (1 / 2) 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.HypergeometricShiftTuran.Result
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
end Reg.D5.S3.Analytic.HypergeometricShiftTuran.Result
