/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionSignedContour
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed bank mass and bounded outer error for the actual reciprocal coefficients. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.AnalyticClosure.Polylogarithm.CompositionCoefficientContour

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionSignedContour

open CompositionReciprocalSeries
open private logIntegrand exp_log_kernel log_integrand_norm actual_log_contour from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionCoefficientContour
open private logLift from D5.S3.AnalyticClosure.Polylogarithm.CompositionFiniteSlit

private theorem horizontal_continuous {g : ℂ → ℂ} {a b y : ℝ}
    (hc : ContinuousOn g (Icc a b ×ℂ Icc 0 (2 * Real.pi)))
    (hy : y ∈ Icc 0 (2 * Real.pi)) :
    ContinuousOn (fun x : ℝ ↦ g (x + y * I)) (Icc a b) := by
  apply hc.comp (by fun_prop)
  intro x hx
  simpa only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, ofReal_im,
    I_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
    using And.intro hx hy

private theorem periodic_kernel (n : ℕ) (x : ℝ) :
    Complex.exp (-(n : ℂ) * (x + 2 * Real.pi * I)) =
      (Real.exp (-(n : ℝ) * x) : ℂ) := by
  rw [exp_log_kernel]
  simp only [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
    ← Complex.ofReal_exp, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  congr 2
  ring

private theorem signed_horizontal {g F G : ℂ → ℂ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hc : ContinuousOn g (Icc a b ×ℂ Icc 0 (2 * Real.pi)))
    (hbot : ∀ x, a ≤ x → x ≤ b → g x = F (Real.exp x))
    (htop : ∀ x, a ≤ x → x ≤ b → g (x + 2 * Real.pi * I) = G (Real.exp x))
    (hcancel : ∀ x, a ≤ x → x ≤ 0 → F (Real.exp x) = G (Real.exp x))
    (hconj : ∀ x, 0 ≤ x → x ≤ b → G (Real.exp x) = conj (F (Real.exp x))) (n : ℕ) :
    (∫ x in a..b, logIntegrand g n x) -
        (∫ x in a..b, logIntegrand g n (x + 2 * Real.pi * I)) =
      (-2 * I) * ((∫ x in 0..b, -(g x).im * Real.exp (-(n : ℝ) * x) : ℝ) : ℂ) := by
  have hc0 : ContinuousOn (fun x : ℝ ↦ g x) (Icc a b) := by
    simpa using horizontal_continuous hc (y := 0) (by constructor <;> positivity)
  have hc2 := horizontal_continuous hc (y := 2 * Real.pi) ⟨by positivity, le_rfl⟩
  have hc2' : ContinuousOn (fun x : ℝ ↦ g (x + 2 * Real.pi * I)) (Icc a b) := by
    simpa only [ofReal_mul, ofReal_ofNat] using hc2
  have hf : ContinuousOn (fun x : ℝ ↦ logIntegrand g n x) (Icc a b) :=
    hc0.fun_mul (by fun_prop)
  have ht : ContinuousOn (fun x : ℝ ↦ logIntegrand g n (x + 2 * Real.pi * I))
      (Icc a b) := hc2'.fun_mul (by fun_prop)
  let jump : ℝ → ℂ := fun x ↦ logIntegrand g n x -
    logIntegrand g n (x + 2 * Real.pi * I)
  have hjc : ContinuousOn jump (Icc a b) := hf.fun_sub ht
  have hker (x : ℝ) : Complex.exp (-(n : ℂ) * (x : ℂ)) =
      (Real.exp (-(n : ℝ) * x) : ℂ) := by
    have he : -(n : ℂ) * (x : ℂ) = ((-(n : ℝ) * x : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he, ← Complex.ofReal_exp]
  have hjleft : (∫ x in a..0, jump x) = 0 := by
    calc
      _ = ∫ _ : ℝ in a..0, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha.le] at hx
        dsimp [jump, logIntegrand]
        rw [hbot x hx.1 (hx.2.trans hb.le), htop x hx.1 (hx.2.trans hb.le),
          hcancel x hx.1 hx.2, periodic_kernel, hker, sub_self]
      _ = 0 := intervalIntegral.integral_zero
  have hjright : (∫ x in 0..b, jump x) =
      (-2 * I) * ((∫ x in 0..b, -(g x).im * Real.exp (-(n : ℝ) * x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hb.le] at hx
    have hbx := hbot x (ha.le.trans hx.1) hx.2
    dsimp [jump, logIntegrand]
    rw [hbx, htop x (ha.le.trans hx.1) hx.2, hconj x hx.1 hx.2, periodic_kernel,
      hker, ← sub_mul, Complex.sub_conj]
    push_cast
    ring
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc (ha.trans hb).le)
    (ht.intervalIntegrable_of_Icc (ha.trans hb).le)]
  change (∫ x in a..b, jump x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hjc.mono (Icc_subset_Icc le_rfl hb.le) |>.intervalIntegrable_of_Icc ha.le)
    (hjc.mono (Icc_subset_Icc ha.le le_rfl) |>.intervalIntegrable_of_Icc hb.le),
    hjleft, zero_add, hjright]

private theorem actual_signed_contour (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ b B : ℝ, 0 < b ∧ ∃ h : ℝ → ℝ,
      ContinuousOn h (Icc 0 b) ∧ h 0 = 0 ∧
      (∀ x, 0 < x → x ≤ b → 0 < h x) ∧
      ∀ n : ℕ, ordinaryCoefficient head tail ell n ≤
        B * Real.exp (-(n : ℝ) * b) -
          (1 / Real.pi) * ∫ x in 0..b, h x * Real.exp (-(n : ℝ) * x) := by
  obtain ⟨R, F, G, hR, hF1, hconj, hneg, hc, hbot, htop, hcancel, hcoeff⟩ :=
    actual_log_contour head tail ell
  let a : ℝ := Real.log (1 / 2)
  let b : ℝ := Real.log R
  let g := logLift F G
  change ContinuousOn g (Icc a b ×ℂ Icc 0 (2 * Real.pi)) at hc
  change ∀ x : ℝ, a ≤ x → x ≤ b → g x = F (Real.exp x) at hbot
  change ∀ x : ℝ, a ≤ x → x ≤ b →
    g (x + 2 * Real.pi * I) = G (Real.exp x) at htop
  have ha : a < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hb : 0 < b := Real.log_pos hR
  have hbc : ContinuousOn (fun x : ℝ ↦ g x) (Icc a b) := by
    simpa only [ofReal_zero, zero_mul, add_zero] using
      horizontal_continuous hc (y := 0) ⟨le_rfl, by positivity⟩
  have hoc : ContinuousOn (fun theta : ℝ ↦ g (b + theta * I)) (Icc 0 (2 * Real.pi)) := by
    apply hc.comp (by fun_prop)
    intro theta htheta
    change ((b : ℂ) + theta * I).re ∈ Icc a b ∧
      ((b : ℂ) + theta * I).im ∈ Icc 0 (2 * Real.pi)
    constructor
    · simpa only [mem_Icc, add_re, ofReal_re, mul_re, I_re, ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero, add_zero] using
        And.intro (ha.trans hb).le (le_refl b)
    · simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] using htheta
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hoc
  let h : ℝ → ℝ := fun x ↦ -(g x).im
  refine ⟨b, B, hb, h, ?_, ?_, ?_, ?_⟩
  · exact (Complex.continuous_im.comp_continuousOn hbc).fun_neg.mono
      (Icc_subset_Icc ha.le le_rfl)
  · simpa only [h, ofReal_zero, Real.exp_zero, ofReal_one, hF1, neg_zero] using
      congrArg (fun z : ℂ ↦ -z.im) (hbot 0 ha.le hb.le)
  · intro x hx hxb
    dsimp [h]
    rw [hbot x (ha.le.trans hx.le) hxb]
    exact neg_pos.mpr (hneg _ (Real.one_lt_exp_iff.mpr hx)
      (by simpa only [b, Real.exp_log (zero_lt_one.trans hR)] using Real.exp_le_exp.mpr hxb))
  · intro n
    have hconj' : ∀ x : ℝ, 0 ≤ x → x ≤ b →
        G (Real.exp x) = conj (F (Real.exp x)) := by
      intro x hx hxb
      exact hconj _ (Real.one_le_exp_iff.mpr hx)
        (by simpa only [b, Real.exp_log (zero_lt_one.trans hR)] using Real.exp_le_exp.mpr hxb)
    have hj := signed_horizontal ha hb hc hbot htop hcancel hconj' n
    let outer : ℂ := ∫ theta : ℝ in 0..2 * Real.pi, logIntegrand g n (b + theta * I)
    have hon : ‖outer‖ ≤ (B * Real.exp (-(n : ℝ) * b)) * (2 * Real.pi) := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 2 * Real.pi) (C := B * Real.exp (-(n : ℝ) * b)) (by
          intro theta htheta
          rw [uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)] at htheta
          rw [log_integrand_norm]
          exact mul_le_mul_of_nonneg_right (hB theta (Ioc_subset_Icc_self htheta))
            (Real.exp_pos _).le)
      simpa only [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using hh
    have heq : (ordinaryCoefficient head tail ell n : ℂ) =
        (1 / (2 * Real.pi) : ℂ) * outer -
          (1 / Real.pi : ℂ) * ((∫ x in 0..b, h x * Real.exp (-(n : ℝ) * x) : ℝ) : ℂ) := by
      have hh := hcoeff n
      rw [add_sub_assoc, hj] at hh
      rw [hh]
      change (2 * (Real.pi : ℂ) * I)⁻¹ * (I * outer + (-2 * I) * _) = _
      dsimp only [h, g]
      field_simp
      <;> ring
    have houter : ((1 / (2 * Real.pi) : ℂ) * outer).re ≤
        B * Real.exp (-(n : ℝ) * b) := by
      calc
        _ ≤ ‖(1 / (2 * Real.pi) : ℂ) * outer‖ := Complex.re_le_norm _
        _ = (1 / (2 * Real.pi)) * ‖outer‖ := by
          rw [norm_mul]
          norm_cast
          rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        _ ≤ (1 / (2 * Real.pi)) *
            ((B * Real.exp (-(n : ℝ) * b)) * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hon (by positivity)
        _ = _ := by field_simp
    have hscale : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hscale' : (1 / Real.pi : ℂ) = ((1 / Real.pi : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hscale, hscale'] at heq
    rw [hscale] at houter
    have hre := congrArg Complex.re heq
    simp only [ofReal_re, sub_re, mul_re, ofReal_im, zero_mul, sub_zero] at hre houter
    linarith

end D5.S3.AnalyticClosure.Polylogarithm.CompositionSignedContour
