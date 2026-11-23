import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Observation of window mass for the characteristic-function bounds. -/

namespace Reg.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
open FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit MeasureTheory Set
open Complex

noncomputable section

abbrev massSignature : Signature :=
  oneRole (Measure ℝ) (fun _ => Set ℝ)

private def actual : Realization massSignature :=
  realize massSignature (fun _ μ W => μ.real W) (fun e => nomatch e)

private def rejected : Realization massSignature :=
  realize massSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence massSignature actual := by
  intro _
  refine ⟨Measure.dirac (0 : ℝ), univ, ∅, ?_⟩
  change (Measure.dirac (0 : ℝ)).real univ ≠ (Measure.dirac (0 : ℝ)).real ∅
  simp [Measure.real]

abbrev gaussianArena : Arena where
  signature := massSignature
  Law A := ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (b r : ℝ) {s : ℝ} (_ : 0 < s),
    let G := ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) *
      (Complex.exp (-I * (2 * t / s : ℝ) * b) * charFun μ (2 * t / s))
    Real.sqrt Real.pi * A.readout () μ {x | |x - b| ≤ r} ≤ Real.exp ((r / s) ^ 2) * ‖G‖ ∧
      ‖G‖ ≤ ∫ t : ℝ, Real.exp (-t ^ 2) * ‖charFun μ (2 * t / s)‖

private theorem violates_gaussian : ¬ gaussianArena.Law rejected := by
  intro law
  obtain ⟨h, _⟩ := law (0 : Measure ℝ) 0 1 (s := 1) zero_lt_one
  change Real.sqrt Real.pi * 1 ≤
    Real.exp ((1 / 1 : ℝ) ^ 2) * ‖∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) *
      (Complex.exp (-I * (2 * t / 1 : ℝ) * 0) * charFun (0 : Measure ℝ) (2 * t / 1))‖ at h
  simp only [charFun_zero_measure, norm_zero, mul_zero, integral_zero, mul_one] at h
  exact (not_le_of_gt (Real.sqrt_pos.2 Real.pi_pos)) h

def gaussianEvidence : Registration gaussianArena
    (type_of% @measureReal_closedWindow_le_gaussian_charFun) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨measureReal_closedWindow_le_gaussian_charFun, rejected, violates_gaussian⟩
  sensitivity := sensitivity gaussianArena.Law actual rejected violates_gaussian
  dependence := dependence

def gaussianRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    measureReal_closedWindow_le_gaussian_charFun (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow.gaussianUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow.gaussianEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianArena⟩
  objectArena := .source ⟨gaussianArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianArena ⟨gaussianEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ μ W => μ.real W) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev quadraticArena : Arena where
  signature := massSignature
  Law A := ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (b : ℝ) {r k : ℝ} (_ : 0 < r) (_ : 0 < k)
      (_ : ∀ t : ℝ, ‖charFun μ t‖ ≤ (1 + k * t ^ 2)⁻¹),
    A.readout () μ {x | |x - b| ≤ r} ≤
      Real.exp (1 / 2) * Real.sqrt Real.pi * (Real.sqrt 2 * r) / (2 * Real.sqrt k)

private theorem violates_quadratic : ¬ quadraticArena.Law rejected := by
  intro law
  have h := law (0 : Measure ℝ) 0 (r := 1) (k := 100) zero_lt_one (by norm_num)
    (fun t => by rw [charFun_zero_measure, norm_zero]; positivity)
  change (1 : ℝ) ≤
    Real.exp (1 / 2) * Real.sqrt Real.pi * (Real.sqrt 2 * 1) / (2 * Real.sqrt 100) at h
  have hsqrt : Real.sqrt 100 = 10 := calc
    _ = Real.sqrt ((10 : ℝ) ^ 2) := congrArg Real.sqrt (by norm_num)
    _ = _ := Real.sqrt_sq (by norm_num)
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    exact Real.pi_lt_four.le
  rw [hsqrt, mul_one] at h
  have hexp : Real.exp (1 / 2) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans Real.exp_one_lt_three.le
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hprod : Real.exp (1 / 2) * Real.sqrt Real.pi * Real.sqrt 2 ≤ 3 * 2 * 2 := by
    exact mul_le_mul (mul_le_mul hexp hpi (Real.sqrt_nonneg _) (by norm_num))
      h2 (Real.sqrt_nonneg _) (by norm_num)
  linarith

def quadraticEvidence : Registration quadraticArena
    (type_of% @measureReal_closedWindow_le_of_quadratic_charFun) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨measureReal_closedWindow_le_of_quadratic_charFun, rejected, violates_quadratic⟩
  sensitivity := sensitivity quadraticArena.Law actual rejected violates_quadratic
  dependence := dependence

def quadraticRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    measureReal_closedWindow_le_of_quadratic_charFun (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow.quadraticUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow.quadraticEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨quadraticArena⟩
  objectArena := .source ⟨quadraticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quadraticArena ⟨quadraticEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ μ W => μ.real W) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms gaussianRegistration
#print axioms quadraticRegistration

end

end Reg.D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
