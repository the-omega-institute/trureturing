import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Observer.Linear.ReflectingHeatInverseSupport
import D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian
import Batteries.Tactic.OpenPrivate

/-! The physical observation window scales the lattice window by the inverse square mesh count. -/

noncomputable section

open Complex MeasureTheory LeanInformationAudit Set
open _root_.Reg.Support
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.InfiniteSincProduct
open _root_.D5.S3.Observer.Linear.ReflectingHeatInterpolation
open _root_.D5.S3.Observer.Linear.ReflectingHeatStripBound
open _root_.D5.S3.Analytic.Hardy.FiniteStripMomentBound (windowNorm)
open scoped ENNReal

namespace Reg.D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n L => L / (n : ℝ) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (_ : Differentiable ℂ M) {L A B C : ℝ} {m : ℕ} (_ : 0 < L) (_ : 0 ≤ A)
    (_ : ∀ z : ℂ, ‖M z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (L / 2 * ‖z‖))
    (_ : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n)
    (_ : (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I) ≠ 0),
    let T := R.readout () n L
    let Aj := (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I)
    let bound := (n : ℝ) * Real.exp (rate n j * L / 2) /
      (weight n j * ‖Aj‖ * Real.sqrt (2 * Real.pi)) *
      Real.sqrt (∫ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ^ 2)
    ∃ u : ℝ → ℝ, MemLp u 2 volume ∧ (∀ s ∉ Icc 0 T, u s = 0) ∧
      (∀ k : Mode n, (∫ s in Ioo 0 T, u s * (weight n k * Real.exp (-physicalRate n k * s))) =
        if k = j then 1 else 0) ∧
      windowNorm T u ≤ bound ∧ Real.sqrt ((physicalGramian n T)⁻¹ j j) ≤ bound

open private outer_root from Reg.D5.S3.Observer.Linear.ReflectingHeatInverseSupport
open private differentiable_complexSinc norm_sinc_strip norm_sinc_mul_one_add_norm from
  D5.S3.Fourier.InverseFourierSupport

private theorem sinc_radial (z : ℂ) :
    ‖complexSinc z‖ ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) * Real.exp (2 / 2 * ‖z‖) := by
  simpa using (by
    simpa using (norm_sinc_strip zero_lt_one z).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z)
        (show (0 : ℝ) ≤ 1 by norm_num))) : ‖complexSinc z‖ ≤ Real.exp ‖z‖)

private theorem sinc_real (ω : ℝ) : ∃ ζ : ℂ, ζ ≠ 0 ∧
    ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
    ‖complexSinc (ω : ℂ)‖ ≤ 18 * (1 + 1 * |ω|) / ‖ζ‖ ^ (2 : ℕ) := by
  obtain ⟨ζ, hζ, he, hn⟩ := outer_root ((ω : ℂ) * I - 2)
  refine ⟨ζ, hζ, he, hn, ?_⟩
  have hx : ‖ζ‖ ≤ 3 * (1 + |ω|) := by
    have hv : ‖ζ⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hn
    have hrewrite : ζ = ((ω : ℂ) * I - 2) - ζ⁻¹ := by rw [← he]; ring
    calc
      ‖ζ‖ ≤ ‖(ω : ℂ) * I - 2‖ + ‖ζ⁻¹‖ := by
        conv_lhs => rw [hrewrite]
        exact norm_sub_le _ _
      _ ≤ (|ω| + 2) + 1 := by
        gcongr
        · exact (norm_sub_le _ _).trans (by simp [Real.norm_eq_abs])
      _ ≤ _ := by linarith [abs_nonneg ω]
  have hs : ‖complexSinc (ω : ℂ)‖ * (1 + |ω|) ≤ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, show (1 : ℝ) + 1 = 2 by norm_num] using
      norm_sinc_mul_one_add_norm zero_lt_one (ω : ℂ)
  apply (le_div_iff₀ (by positivity : 0 < ‖ζ‖ ^ (2 : ℕ))).mpr
  calc
    _ ≤ ‖complexSinc (ω : ℂ)‖ * (3 * (1 + |ω|)) ^ 2 := by gcongr
    _ = 9 * (1 + |ω|) * (‖complexSinc (ω : ℂ)‖ * (1 + |ω|)) := by ring
    _ ≤ 9 * (1 + |ω|) * 2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

private theorem two_cell_node_ne_zero :
    ((nodalDerivative 2 (0 : Mode 2) : ℝ) : ℂ) *
      complexSinc (-(rate 2 (0 : Mode 2) : ℂ) * I) ≠ 0 := by
  have hn : nodalDerivative 2 (0 : Mode 2) = 1 := by
    unfold nodalDerivative
    have he : (Finset.univ.erase (0 : Mode 2)) = ∅ := by decide
    rw [he, Finset.prod_empty]
  rw [hn, ofReal_one, one_mul]
  have hq := rate_pos 2 (0 : Mode 2)
  have hz : -(rate 2 (0 : Mode 2) : ℂ) * I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr hq.ne')) I_ne_zero
  rw [complexSinc_of_ne_zero hz, sin_mul_I, ← ofReal_neg, ← ofReal_sinh]
  have hsinh : Real.sinh (-rate 2 (0 : Mode 2)) ≠ 0 := by
    rw [Real.sinh_neg]
    exact neg_ne_zero.mpr (Real.sinh_pos_iff.mpr hq).ne'
  exact div_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hsinh) I_ne_zero) (by
    simpa only [ofReal_neg] using hz)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨u, _, _, hm, _, _⟩ := h 2 (0 : Mode 2) complexSinc differentiable_complexSinc
    (L := 2) (A := 18) (B := 1) (C := 1) (m := 0) (by norm_num) (by norm_num)
    sinc_radial sinc_real two_cell_node_ne_zero
  have he := hm (0 : Mode 2)
  change (∫ s in Ioo (0 : ℝ) 0, _) = if (0 : Mode 2) = 0 then 1 else 0 at he
  simp at he

def family : Registration arena (type_of% @inverse_diagonal_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse_diagonal_upper_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
    have h : (0 : ℝ) / (2 : ℝ) ^ 2 ≠ 1 / (2 : ℝ) ^ 2 := by
      rw [zero_div]
      exact ne_of_lt (div_pos zero_lt_one (by positivity))
    exact h

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@inverse_diagonal_upper_bound) (Realization signature) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.Observer.Linear.ReflectingHeatInterpolation.inverse_diagonal_upper_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n L => L / (n : ℝ) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.Linear.ReflectingHeatPhysicalGramian
