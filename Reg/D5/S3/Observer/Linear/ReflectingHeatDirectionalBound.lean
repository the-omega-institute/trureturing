import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.ReflectingHeatDirectionalBound
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! The polynomial part of the contour bound depends on the norm of the contour point. -/

noncomputable section

open Complex MeasureTheory LeanInformationAudit
open _root_.Reg.Support
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.ReflectingHeatInterpolation
open _root_.D5.S3.Observer.Linear.ReflectingHeatStripBound

namespace Reg.D5.S3.Observer.Linear.ReflectingHeatDirectionalBound

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => 1 + ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (_hM_entire : Differentiable ℂ M) {L A B C : ℝ} {m : ℕ} (_hL : 0 ≤ L) (_hA : 0 ≤ A)
    (_hM_radial : ∀ z : ℂ, ‖M z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (L / 2 * ‖z‖))
    (_hM_real : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n),
    Differentiable ℂ (momentInterpolant n j M) ∧
    MemLp (fun ω : ℝ => momentInterpolant n j M (ω : ℂ)) 2 volume ∧
    (∫ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ^ 2) ≤
      2 * ((n : ℝ) * A) ^ 2 * Real.pi * ((n : ℝ) ^ 2 / 4 + 2 * B ^ 2) ∧
    (∀ z : ℂ, ‖momentInterpolant n j M z‖ ≤
      max ((n : ℝ) * A * ((rate n j)⁻¹ + |B|)) (4 ^ (n - 2) * C) *
        R.readout () () z ^ (n - 2 + m) * Real.exp (L / 2 * |z.im|)) ∧
    (∀ k : Mode n, momentInterpolant n j M (-(rate n k : ℂ) * I) =
      if k = j then (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I) else 0)

private theorem outer_root (c : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = c ∧ 1 ≤ ‖z‖ := by
  obtain ⟨w, hw⟩ := Complex.cos_surjective (c / 2)
  let z := Complex.exp (w * I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have he : z + z⁻¹ = c := by
    simp only [Complex.cos, neg_mul, Complex.exp_neg] at hw
    change z + z⁻¹ = c
    have h := congrArg (fun x : ℂ => x * 2) hw
    simpa only [div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using h
  by_cases hn : 1 ≤ ‖z‖
  · exact ⟨z, hz, he, hn⟩
  · exact ⟨z⁻¹, inv_ne_zero hz, by simpa only [inv_inv, add_comm] using he, by
      rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.2 hz)).2 (le_of_not_ge hn)⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 0 (fun _ => 0) (differentiable_const (0 : ℂ))
    (L := 0) (A := 0) (B := 0) (C := 1) (m := 1) le_rfl le_rfl (by
      intro z
      simp only [norm_zero]
      positivity) (by
      intro ω
      obtain ⟨ζ, hζ, he, hn⟩ := outer_root ((ω : ℂ) * I - 2)
      exact ⟨ζ, hζ, he, hn, by simp⟩)
  have he := hh.2.2.2.1 0
  change ‖momentInterpolant 2 0 (fun _ => 0) 0‖ ≤
    max ((2 : ℝ) * 0 * ((rate 2 (0 : Mode 2))⁻¹ + |(0 : ℝ)|)) (4 ^ ((2 : ℕ) - 2) * 1) *
      (-1 : ℝ) ^ ((2 : ℕ) - 2 + 1) * Real.exp (0 / 2 * |(0 : ℂ).im|) at he
  norm_num [momentInterpolant] at he

def family : Registration arena (type_of% @momentInterpolant_contour_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨momentInterpolant_contour_bounds, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    change (1 : ℝ) + ‖(0 : ℂ)‖ ≠ 1 + ‖(1 : ℂ)‖
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@momentInterpolant_contour_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.momentInterpolant_contour_bounds.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatDirectionalBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => 1 + ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatDirectionalBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body",
        "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.Linear.ReflectingHeatDirectionalBound
