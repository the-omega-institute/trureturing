import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockDefs
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
  have g2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have g3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have g4 : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have g32 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = ((1 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
    norm_num [Nat.doubleFactorial]
  have g52 : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
    rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
    norm_num [Nat.doubleFactorial]
  have g72 : Real.Gamma (7 / 2) = 15 * Real.sqrt Real.pi / 8 := by
    rw [show (7 / 2 : ℝ) = ((3 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.Gamma_nat_add_half]
    norm_num [Nat.doubleFactorial]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hvalue :
      twoBlockTuranCoeff (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0)
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 / 2 : ℝ))
        1 (1 / 2) (1 / 2) 1 =
        45 * (Real.sqrt Real.pi) ^ 2 / 32 -
          32 / (5 * (Real.sqrt Real.pi) ^ 2) -
          64 / (9 * (Real.sqrt Real.pi) ^ 2) := by
    norm_num [twoBlockTuranCoeff, seriesCoeff, pochRatio,
      _root_.D5.S3.Analytic.HypergeometricShiftTuran.Defs.coeff,
      Finset.sum_range_succ, g2, g3, g4, g32, g52, g72]
    <;> field_simp [ne_of_gt hs] <;> ring
  rw [hvalue]
  simp only [Real.sq_sqrt Real.pi_pos.le]
  have hr : 45 * Real.pi / 32 - 32 / (5 * Real.pi) - 64 / (9 * Real.pi) =
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
