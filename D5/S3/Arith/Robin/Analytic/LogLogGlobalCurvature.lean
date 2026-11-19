/- GID: D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LogLogGlobalCurvature
   mirror-E: none(waiver:global-real-analysis)
   anchors: []
   utility: none
   digest: Full-domain quadratic tangent-gap envelope for the log-log kernel. -/

/- The density and reciprocal logarithmic kernel are existing project objects.
   The proof compares second derivatives of quadratic-corrected tangent gaps;
   it does not assume an integral representation or a curvature envelope. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.Convex.Deriv

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature

open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity g_has_deriv_at)
open D5.S3.Arith.Robin.ArithmeticMixedCornerResponse (density_antitone)

/-- The full-domain quadratic tangent-gap sandwich for log-log.
The endpoints can coincide, or occur in either order; there is no displacement
bound. The coefficient is the existing activation density at each endpoint.
-/
theorem loglog_tangent_gap_quadratic {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    let K := Real.log (Real.log a) + (b - a) / (a * Real.log a) -
      Real.log (Real.log b)
    let w := fun t : ℝ => (1 + Real.log t) / (t ^ 2 * (Real.log t) ^ 2)
    w (max a b) * (b - a) ^ 2 / 2 ≤ K ∧
      K ≤ w (min a b) * (b - a) ^ 2 / 2 := by
  dsimp only
  by_cases heq : a = b
  · subst b
    simp
  let l : ℝ := min a b
  let u : ℝ := max a b
  have haI : a ∈ Icc l u := ⟨min_le_left a b, le_max_left a b⟩
  have hbI : b ∈ Icc l u := ⟨min_le_right a b, le_max_right a b⟩
  have hlu : l ≤ u := (min_le_left a b).trans (le_max_left a b)
  have hlI : l ∈ Icc l u := left_mem_Icc.mpr hlu
  have hdomain : ∀ t ∈ Icc l u, 1 < t := by
    intro t ht
    exact (lt_min ha hb).trans_le ht.1
  have hlowDensity : ∀ t ∈ Icc l u, activationDensity u ≤ activationDensity t :=
    fun t ht => density_antitone (hdomain t ht) ht.2
  have huppDensity : ∀ t ∈ Icc l u, activationDensity t ≤ activationDensity l :=
    fun t ht => density_antitone (hdomain l hlI) ht.1

  /- Taylor comparison bridge, including a stationary point at an endpoint.
  The actual Mathlib second-derivative criterion supplies convexity; the two
  secant APIs handle both orders without a sign assumption on b-a. -/
  have hstationary (F F' F'' : ℝ → ℝ)
      (hF : ∀ t ∈ Icc l u, HasDerivAt F (F' t) t)
      (hF' : ∀ t ∈ Icc l u, HasDerivAt F' (F'' t) t)
      (hF'' : ∀ t ∈ Icc l u, 0 ≤ F'' t)
      (hzero : F' a = 0) : F a ≤ F b := by
    have hcv : ConvexOn ℝ (Icc l u) F :=
      convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u)
        (HasDerivAt.continuousOn hF)
        (fun t ht => (hF t (interior_subset ht)).hasDerivWithinAt)
        (fun t ht => (hF' t (interior_subset ht)).hasDerivWithinAt)
        (fun t ht => hF'' t (interior_subset ht))
    rcases lt_or_gt_of_ne heq with hab | hba
    · have hs := hcv.le_slope_of_hasDerivAt haI hbI hab (hF a haI)
      rw [hzero, slope_def_field] at hs
      have hdiff := (le_div_iff₀ (sub_pos.mpr hab)).mp hs
      linarith
    · have hs := hcv.slope_le_of_hasDerivAt hbI haI hba (hF a haI)
      rw [hzero, slope_def_field] at hs
      have hdiff := (div_le_iff₀ (sub_pos.mpr hba)).mp hs
      linarith

  let R : ℝ → ℝ → ℝ := fun c t =>
    Real.log (Real.log a) + (t - a) * g a - Real.log (Real.log t) -
      c * (t - a) ^ 2 / 2
  let V : ℝ → ℝ → ℝ := fun c t => g a - g t - c * (t - a)
  have hline (t : ℝ) : HasDerivAt (fun x : ℝ => x - a) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const a
  have hloglog (t : ℝ) (ht : 1 < t) :
      HasDerivAt (fun x : ℝ => Real.log (Real.log x)) (g t) t := by
    have ht0 : t ≠ 0 := ne_of_gt (by linarith : 0 < t)
    have ht1 : t ≠ 1 := ne_of_gt ht
    have htm1 : t ≠ -1 := by linarith
    simpa [g, one_div, div_eq_mul_inv, mul_inv_rev, mul_comm] using
      Real.hasDerivAt_log_log ht0 ht1 htm1
  have hR (c : ℝ) : ∀ t ∈ Icc l u, HasDerivAt (R c) (V c t) t := by
    intro t ht
    have hd := (((hasDerivAt_const t (Real.log (Real.log a))).add
      ((hline t).mul_const (g a))).sub (hloglog t (hdomain t ht))).sub
      ((((hline t).pow 2).const_mul c).div_const 2)
    apply hd.congr_deriv
    dsimp only [V]
    norm_num <;> ring
  have hV (c : ℝ) : ∀ t ∈ Icc l u,
      HasDerivAt (V c) (activationDensity t - c) t := by
    intro t ht
    have hd := ((g_has_deriv_at (hdomain t ht)).const_sub (g a)).sub
      ((hline t).const_mul c)
    apply hd.congr_deriv
    ring
  have hRa (c : ℝ) : R c a = 0 := by simp [R]
  have hVa (c : ℝ) : V c a = 0 := by simp [V]

  have hlower : 0 ≤ R (activationDensity u) b := by
    have h := hstationary (R (activationDensity u)) (V (activationDensity u))
      (fun t => activationDensity t - activationDensity u)
      (hR (activationDensity u)) (hV (activationDensity u))
      (fun t ht => sub_nonneg.mpr (hlowDensity t ht)) (hVa (activationDensity u))
    rwa [hRa] at h
  have hupper : R (activationDensity l) b ≤ 0 := by
    have h := hstationary (fun t => -R (activationDensity l) t)
      (fun t => -V (activationDensity l) t)
      (fun t => -(activationDensity t - activationDensity l))
      (fun t ht => (hR (activationDensity l) t ht).neg)
      (fun t ht => (hV (activationDensity l) t ht).neg)
      (fun t ht => by linarith [huppDensity t ht])
      (by rw [hVa, neg_zero])
    rw [hRa, neg_zero] at h
    linarith

  dsimp only [R, g, l, u] at hlower hupper
  simp only [mul_one_div] at hlower hupper
  simpa only [activationDensity, add_comm] using
    (show activationDensity (max a b) * (b - a) ^ 2 / 2 ≤
        Real.log (Real.log a) + (b - a) / (a * Real.log a) - Real.log (Real.log b) ∧
      Real.log (Real.log a) + (b - a) / (a * Real.log a) - Real.log (Real.log b) ≤
        activationDensity (min a b) * (b - a) ^ 2 / 2 from
      ⟨by linarith only [hlower], by linarith only [hupper]⟩)

end D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
