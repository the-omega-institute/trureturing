/- GID: D5/S3/Weil/ZetaExplicit/LandauLeftVertical
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaExplicit/LandauLeftVertical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An oscillatory logarithm bound for the left vertical integral of a finite Landau contour. -/

import OmegaBuild.Commands
import D5.S3.Weil.Mertens.Cryptids.DigammaBinet
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

compile_only_with_mathlib

namespace D5.S3.Weil.ZetaExplicit.LandauLeftVertical

open Complex MeasureTheory
open scoped Real
open ConjectureMachines.Semantics.Riemann.DigammaBinet

/-- Integration by parts keeps the logarithmic growth in the endpoint and derivative terms. -/
private theorem norm_integral_log_mul_exp_le {g V : ℝ} (hg : 0 < g) (hV : 1 ≤ V) :
    ‖∫ t in 1..V, Complex.log ((3 / 4 : ℂ) + t * I) *
      Complex.exp (((g : ℂ) * I) * t)‖ ≤ 20 * (1 + Real.log V) / g := by
  let z (t : ℝ) := (3 / 4 : ℂ) + t * I
  let f (t : ℝ) := Complex.log (z t)
  let d (t : ℝ) := (z t)⁻¹ * I
  let k := (g : ℂ) * I
  let wave (t : ℝ) := Complex.exp (k * t)
  let prim (t : ℝ) := wave t / k
  have hk : k ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hg.ne') I_ne_zero
  have hkNorm : ‖k‖ = g := by simp [k, abs_of_pos hg]
  have waveNorm (t : ℝ) : ‖wave t‖ = 1 := by simp [wave, k, Complex.norm_exp]
  have primNorm (t : ℝ) : ‖prim t‖ = g⁻¹ := by
    simp [prim, waveNorm, hkNorm, one_div]
  have zz (t : ℝ) : 0 < (z t).re := by norm_num [z]
  have d₁ (t : ℝ) : HasDerivAt f (d t) t := by
    have hz : HasDerivAt (fun w : ℂ => (3 / 4 : ℂ) + w * I) I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (3 / 4 : ℂ)
    exact ((Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl (zz t)))).comp (t : ℂ) hz).comp_ofReal
  have d₂ (t : ℝ) : HasDerivAt prim (wave t) t := by
    have he := ((Complex.hasDerivAt_exp (k * (t : ℂ))).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).const_mul k)).div_const k
    simpa [prim, wave, mul_div_cancel_right₀ _ hk] using he.comp_ofReal
  have cz : Continuous z := by unfold z; fun_prop
  have cd : Continuous d := (cz.inv₀ fun t => fun h => by simpa [h] using zz t).mul continuous_const
  have cw : Continuous wave := by unfold wave; fun_prop
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun t => (d₁ t).continuousAt
  have cp : Continuous prim := continuous_iff_continuousAt.mpr fun t => (d₂ t).continuousAt
  have e := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (1 : ℝ)) (b := V) cf.continuousOn cp.continuousOn (fun t _ => d₁ t)
    (fun t _ => d₂ t) (cd.intervalIntegrable 1 V) (cw.intervalIntegrable 1 V)
  have hb₁ : ‖f 1‖ ≤ Real.log 3 + Real.pi := by
    simpa [f, z, show (1 : ℝ) + 2 = 3 by norm_num] using norm_log_three_fourths_add_mul_I_le 1
  have hbV : ‖f V‖ ≤ Real.log (V + 2) + Real.pi := by
    simpa [f, z, abs_of_nonneg (by linarith : 0 ≤ V)] using norm_log_three_fourths_add_mul_I_le V
  have hbound (t : ℝ) (ht : t ∈ Set.Icc 1 V) : ‖d t * prim t‖ ≤ (t * g)⁻¹ := by
    have h₀ : 0 < t := zero_lt_one.trans_le ht.1
    have hnorm : t ≤ ‖z t‖ := by simpa [z] using (Complex.im_le_norm (z t))
    rw [norm_mul, primNorm]
    dsimp only [d]
    rw [norm_mul, norm_inv, norm_I, mul_one, mul_inv_rev, mul_comm]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h₀ hnorm) (inv_nonneg.mpr hg.le)
  have hdiv : IntervalIntegrable (fun t : ℝ => (t * g)⁻¹) volume 1 V := by
    rw [show (fun t : ℝ => (t * g)⁻¹) = (fun t => t⁻¹ * g⁻¹) by ext t; rw [mul_inv_rev, mul_comm]]
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_inv₀.mono ?_).mul continuousOn_const
    intro t ht
    rw [Set.uIcc_of_le hV] at ht
    exact (zero_lt_one.trans_le ht.1).ne'
  have hrest : ‖∫ t in 1..V, d t * prim t‖ ≤ Real.log V * g⁻¹ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hV).trans ?_
    refine (intervalIntegral.integral_mono_on hV ((cd.mul cp).norm.intervalIntegrable 1 V)
      hdiv hbound).trans_eq ?_
    simp_rw [mul_inv_rev, mul_comm g⁻¹]
    rw [intervalIntegral.integral_mul_const, integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hV), div_one]
  have hlogV : Real.log (V + 2) ≤ Real.log V + Real.log 3 := by
    rw [← Real.log_mul (zero_lt_one.trans_le hV).ne' (by norm_num : (3:ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
  change ‖∫ t in 1..V, f t * wave t‖ ≤ _
  rw [e, div_eq_mul_inv]
  calc
    _ ≤ ‖f V * prim V‖ + ‖f 1 * prim 1‖ + ‖∫ t in 1..V, d t * prim t‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((Real.log (V + 2) + Real.pi) + (Real.log 3 + Real.pi) + Real.log V) * g⁻¹ := by
      rw [norm_mul, primNorm, norm_mul, primNorm, add_mul, add_mul]
      gcongr
    _ ≤ _ := by
      gcongr
      linarith [Real.pi_le_four, Real.log_nonneg hV]

/-- The reflected zeta term and the digamma correction remain bounded after cancelling the
growing logarithm in the functional equation. -/
private theorem norm_left_logDeriv_add_log_le (t : ℝ) :
    ‖logDeriv riemannZeta ((-1 / 4 : ℂ) + t * I) +
      Complex.log ((3 / 4 : ℂ) + t * I)‖ ≤ 80 := by
  let s : ℂ := (-1 / 4 : ℂ) + t * I
  let w : ℂ := (3 / 4 : ℂ) + t * I
  have hsw : s + 1 = w := by dsimp [s, w]; ring
  have hs_nat (n : ℕ) : s ≠ -(n : ℂ) := by simpa [s] using leftVertical_ne_intCast t (-n)
  have h_refl : (1 - s).re = 5 / 4 := by simp [s]; ring
  have h_reflected : ‖logDeriv riemannZeta (1 - s)‖ ≤ 64 := by
    have h := norm_logDeriv_riemannZeta_le_of_one_lt_re (z := 1 - s) (by rw [h_refl]; norm_num)
    rw [h_refl, ofReal_div, ofReal_ofNat, ofReal_ofNat] at h
    exact h.trans norm_logDeriv_riemannZeta_five_fourths_le
  have hlog : ‖Complex.log (2 * π)‖ ≤ 7 := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_log hp.le, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
    linarith [Real.log_le_sub_one_of_pos hp, Real.pi_lt_four]
  have hw : 0 < w.re := by simp [w]
  have hw_norm : 3 / 4 ≤ ‖w‖ := by simpa [w] using re_le_norm w
  have hbinet : ‖Complex.digamma w - Complex.log w‖ ≤ 2 := by
    refine (norm_digamma_sub_log_le_two_add_pi_div_four_norm hw).trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have hs_norm : 1 / 4 ≤ ‖s‖ := by
    have h := abs_re_le_norm s
    have hre : s.re = -1 / 4 := by simp [s]
    rw [hre] at h
    norm_num at h ⊢
    exact h
  have hinv : ‖s⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hs_norm
  have htan : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 2 := by
    rw [norm_mul, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_ofNat]
    have ht := (cos_ne_zero_and_norm_tan_le_one_leftVertical t).2
    calc
      _ ≤ Real.pi / 2 * 1 := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ _ := by linarith [Real.pi_lt_four]
  have hfe := logDeriv_riemannZeta_one_sub (leftVertical_ne_intCast t)
    (riemannZeta_leftVertical_ne_zero t)
  have hd := Complex.digamma_apply_add_one s hs_nat
  rw [hsw] at hd
  change ‖logDeriv riemannZeta s + Complex.log w‖ ≤ _
  have heq : logDeriv riemannZeta s + Complex.log w =
      (((-logDeriv riemannZeta (1 - s) + Complex.log (2 * π)) -
        (Complex.digamma w - Complex.log w)) + s⁻¹) +
        (π / 2 * Complex.tan (π * s / 2)) := by
    change logDeriv riemannZeta s = _ at hfe
    rw [hfe]
    linear_combination hd
  rw [heq]
  have h₁ := norm_add_le (-logDeriv riemannZeta (1 - s)) (Complex.log (2 * π))
  have h₂ := norm_sub_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π))
    (Complex.digamma w - Complex.log w)
  have h₃ := norm_add_le
    (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) -
      (Complex.digamma w - Complex.log w)) s⁻¹
  have h₄ := norm_add_le
    (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) -
      (Complex.digamma w - Complex.log w) + s⁻¹)
    (π / 2 * Complex.tan (π * s / 2))
  rw [norm_neg] at h₁
  linarith

/-- A bound for the finite Landau contour on the line with real part `-1/4`. The
linear term comes from a bounded remainder and the reciprocal frequency term from the
oscillatory logarithm. -/
theorem norm_left_vertical_integral {x V : ℝ} (hx : 1 < x) (hV : 1 ≤ V) :
    ‖∫ t in 1..V, (x : ℂ) ^ ((-1 / 4 : ℂ) + t * I) *
      (-logDeriv riemannZeta ((-1 / 4 : ℂ) + t * I))‖ ≤
      let logBase := Real.log
      x ^ (-1 / 4 : ℝ) * (80 * (V - 1) + 20 * (1 + Real.log V) / logBase x) := by
  let s (t : ℝ) : ℂ := (-1 / 4 : ℂ) + t * I
  let w (t : ℝ) : ℂ := (3 / 4 : ℂ) + t * I
  let wave (t : ℝ) : ℂ := Complex.exp (((Real.log x : ℂ) * I) * t)
  let rest (t : ℝ) : ℂ := logDeriv riemannZeta (s t) + Complex.log (w t)
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hxlog : 0 < Real.log x := Real.log_pos hx
  have hs : Continuous s := by unfold s; fun_prop
  have hw : Continuous w := by unfold w; fun_prop
  have hw_re (t : ℝ) : 0 < (w t).re := by norm_num [w]
  have hwlog : Continuous fun t => Complex.log (w t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (Complex.hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inl (hw_re t)))).continuousAt.comp
        hw.continuousAt
  have hwave : Continuous wave := by unfold wave; fun_prop
  have hrest : Continuous rest := by
    refine Continuous.add (continuous_iff_continuousAt.mpr fun t => ?_) hwlog
    have hne : s t ≠ 1 := by simpa [s] using leftVertical_ne_intCast t 1
    have han : AnalyticAt ℂ riemannZeta (s t) :=
      analyticOn_riemannZeta (s t) hne
    rw [show (fun t => logDeriv riemannZeta (s t)) =
      (fun z => deriv riemannZeta z / riemannZeta z) ∘ s by ext; rw [logDeriv_apply]; rfl]
    exact (han.deriv.continuousAt.div han.continuousAt
      (riemannZeta_leftVertical_ne_zero t)).comp hs.continuousAt
  have hwave_norm (t : ℝ) : ‖wave t‖ = 1 := by simp [wave, norm_exp]
  have hpow (t : ℝ) : (x : ℂ) ^ s t =
      ((x ^ (-1 / 4 : ℝ) : ℝ) : ℂ) * wave t := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx₀.ne'), ← ofReal_log hx₀.le]
    have he : (Real.log x : ℂ) * s t =
        ((Real.log x * (-1 / 4) : ℝ) : ℂ) + ((Real.log x : ℂ) * I) * t := by
      push_cast
      dsimp [s]
      ring
    rw [he, exp_add, ← ofReal_exp, ← Real.rpow_def_of_pos hx₀]
  have hsplit (t : ℝ) : (x : ℂ) ^ s t * (-logDeriv riemannZeta (s t)) =
      ((x ^ (-1 / 4 : ℝ) : ℝ) : ℂ) * (Complex.log (w t) * wave t - rest t * wave t) := by
    rw [hpow]
    dsimp [rest]
    ring
  have hl : ‖∫ t in 1..V, Complex.log (w t) * wave t‖ ≤
      20 * (1 + Real.log V) / Real.log x :=
    norm_integral_log_mul_exp_le hxlog hV
  have hr : ‖∫ t in 1..V, rest t * wave t‖ ≤ 80 * (V - 1) := by
    rw [← abs_of_nonneg (sub_nonneg.mpr hV)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => rest t * wave t) ?_
    intro t _
    rw [norm_mul, hwave_norm, mul_one]
    exact norm_left_logDeriv_add_log_le t
  change ‖∫ t in 1..V, (x : ℂ) ^ s t * (-logDeriv riemannZeta (s t))‖ ≤ _
  simp_rw [hsplit]
  have hi := intervalIntegral.integral_sub
    ((hwlog.mul hwave).intervalIntegrable (μ := volume) 1 V)
    ((hrest.mul hwave).intervalIntegrable (μ := volume) 1 V)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul, norm_mul, norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), hi]
  gcongr
  exact (norm_sub_le _ _).trans (by simpa [add_comm] using add_le_add hl hr)

end D5.S3.Weil.ZetaExplicit.LandauLeftVertical
