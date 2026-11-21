import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Observer.Linear.ReflectingHeatInverseSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! The inverse uses the angular-to-cycles frequency restriction. -/

noncomputable section

open Complex MeasureTheory LeanInformationAudit
open _root_.Reg.Support
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.InverseFourierSupport
open scoped ENNReal
open _root_.D5.S3.Observer.Linear.ReflectingHeatInterpolation
open _root_.D5.S3.Observer.Linear.ReflectingHeatStripBound

namespace Reg.D5.S3.Observer.Linear.ReflectingHeatInverseSupport

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ) (fun _ => ℝ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ F => frequencyRestriction F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (_hM_entire : Differentiable ℂ M) {L A B C : ℝ} {m : ℕ} (_hL : 0 ≤ L) (_hA : 0 ≤ A)
    (_hM_radial : ∀ z : ℂ, ‖M z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (L / 2 * ‖z‖))
    (_hM_real : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n),
    let g := R.readout () () (momentInterpolant n j M)
    ∃ hg : MemLp g 2 volume,
      ∃ v : ℝ → ℂ, Integrable v ∧
        (v =ᵐ[volume] (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg.toLp g)) ∧
        (∀ t : ℝ, L / 2 < |t| → v t = 0) ∧
        (∀ z : ℂ, (∫ t : ℝ, exp (-I * z * (t : ℂ)) * v t) = momentInterpolant n j M z) ∧
        (∀ k : Mode n, (∫ t : ℝ, exp (-(rate n k : ℂ) * (t : ℂ)) * v t) =
          if k = j then (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I) else 0)

private theorem outer_root (c : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = c ∧ 1 ≤ ‖z‖ := by
  obtain ⟨w, hw⟩ := Complex.cos_surjective (c / 2)
  let z := Complex.exp (w * I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have he : z + z⁻¹ = c := by
    simp only [Complex.cos, neg_mul, Complex.exp_neg] at hw
    have h := congrArg (fun x : ℂ => x * 2) hw
    simpa only [z, div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using h
  by_cases hn : 1 ≤ ‖z‖
  · exact ⟨z, hz, he, hn⟩
  · exact ⟨z⁻¹, inv_ne_zero hz, by simpa only [inv_inv, add_comm] using he, by
      rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.2 hz)).2 (le_of_not_ge hn)⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hg, _⟩ := h 2 0 (fun _ => 0) (differentiable_const (0 : ℂ))
    (L := 0) (A := 0) (B := 0) (C := 1) (m := 0) le_rfl le_rfl (by simp) (by
      intro ω
      obtain ⟨ζ, hζ, he, hn⟩ := outer_root ((ω : ℂ) * I - 2)
      exact ⟨ζ, hζ, he, hn, by simp⟩)
  have hconst : MemLp (fun _ : ℝ => (1 : ℂ)) 2 volume := hg
  simpa [memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top,
    Real.volume_univ] using hconst

def family : Registration arena (type_of% @momentInterpolant_inverse_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨momentInterpolant_inverse_support, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hz := congrFun h 0
    change frequencyRestriction (fun _ => 0) 0 = frequencyRestriction (fun _ => 1) 0 at hz
    simp [frequencyRestriction] at hz

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@momentInterpolant_inverse_support) (Realization signature) Type Unit where
  unitName := `D5.S3.Observer.Linear.ReflectingHeatInterpolation.momentInterpolant_inverse_support.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatInverseSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => frequencyRestriction F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatInverseSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.Linear.ReflectingHeatInverseSupport
