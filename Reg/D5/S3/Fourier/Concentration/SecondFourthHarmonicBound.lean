import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.SecondFourthHarmonicBound

/-! Dependence of the attained first harmonic bound on the two prescribed caps. -/

namespace Reg.D5.S3.Fourier.Concentration.SecondFourthHarmonicBound

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.SecondFourthHarmonicBound
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ caps => harmonicBound caps) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (e k : ℝ) (_ : 0 ≤ e) (_ : e ≤ 1) (_ : 0 ≤ k) (_ : k ≤ 1),
    let bound := V.readout () () (e, k)
    (∀ {ι : Type u} [Fintype ι] (w : ι → ℝ)
      (_ : ∀ j, 0 ≤ w j) (_ : ∑ j, w j = 1) (z : ι → ℂ) (_ : ∀ j, ‖z j‖ = 1),
      ‖harmonic w z 2‖ ≤ e → ‖harmonic w z 4‖ ≤ k → ‖harmonic w z 1‖ ≤ bound) ∧
    (∃ (w : Fin 3 → ℝ) (z : Fin 3 → ℂ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, ‖z j‖ = 1) ∧ ‖harmonic w z 2‖ ≤ e ∧ ‖harmonic w z 4‖ ≤ k ∧
        ‖harmonic w z 1‖ = bound)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h (n : ℕ) :
      harmonic (fun _ : ULift.{u} (Fin 1) => 1) (fun _ => 1) n = 1 := by
    simp [harmonic]
  have hupper := (law 1 1 (by norm_num) le_rfl (by norm_num) le_rfl).1
    (fun _ : ULift.{u} (Fin 1) => 1) (fun _ => by norm_num) (by simp)
    (fun _ => 1) (fun _ => norm_one)
    (by rw [h, norm_one]) (by rw [h, norm_one])
  rw [h, norm_one] at hupper
  norm_num [rejected, realize] at hupper

private theorem bound_zero_zero : harmonicBound (0, 0) = (2 / 3 : ℝ) := by
  unfold harmonicBound
  dsimp only
  rw [min_eq_left (Real.sqrt_nonneg _), ite_eq_right zero_ne_one]
  have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have horder : Real.sqrt (1 / 4 : ℝ) ≤ Real.sqrt (1 / 2 : ℝ) :=
    Real.sqrt_le_sqrt (by norm_num)
  norm_num only [zero_add, sub_zero, mul_one]
  rw [min_eq_right horder, hquarter]
  norm_num

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (0, 0), (1, 1), ?_⟩
  change harmonicBound (0, 0) ≠ harmonicBound (1, 1)
  rw [bound_zero_zero]
  norm_num [harmonicBound]

def evidence : Registration arena.{u} (type_of% @sharp_second_fourth_harmonic_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_second_fourth_harmonic_bound.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sharp_second_fourth_harmonic_bound.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.SecondFourthHarmonicBound.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.SecondFourthHarmonicBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ caps => harmonicBound caps) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.SecondFourthHarmonicBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.SecondFourthHarmonicBound
