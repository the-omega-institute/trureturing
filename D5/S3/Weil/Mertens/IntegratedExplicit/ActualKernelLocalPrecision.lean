/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third derivative and strict local logarithmic curvature of the actual arithmetic kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Literal arithmetic derivative and logarithmic curvature controls on one cusp window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision

open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

def D3 (t : ℝ) : ℝ :=
  D1 t / 4 - Real.exp (t / 2) / 2 -
    Real.exp (-t / 2) / (2 * (Real.exp (2 * t) - 1)) -
    2 * Real.exp (3 * t / 2) / (Real.exp (2 * t) - 1) ^ 2

lemma hasDerivAt_D2 {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt D2 (D3 t) t := by
  have hd : Real.exp (2 * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))).ne'
  have h := (((hasDerivAt_K ht ht2).div_const 4).sub
    (((hasDerivAt_id t).div_const 2).exp)).add
      ((((hasDerivAt_id t).neg.div_const 2).exp).div
        ((((hasDerivAt_id t).const_mul 2).exp).sub_const 1) hd)
  convert h using 1
  · rfl
  · have he : Real.exp (3 * t / 2) = Real.exp (-t / 2) * Real.exp (2 * t) := by
      rw [← Real.exp_add]; congr 1; ring
    dsimp [D3]
    rw [he]
    have htw : t * 2 = 2 * t := by ring
    simp only [id_eq] at h ⊢
    have hsq : 1 - 2 * Real.exp (2 * t) + Real.exp (2 * t) ^ 2 ≠ 0 := by
      have hne : Real.exp (2 * t) - 1 ≠ 0 := hd
      nlinarith [sq_pos_of_ne_zero hne]
    have he2 : Real.exp (t * 2) = Real.exp (2 * t) := by congr 1 <;> ring
    have hd' : Real.exp (t * 2) - 1 ≠ 0 := by rw [he2]; exact hd
    have hsq' : 1 - 2 * Real.exp (t * 2) + Real.exp (t * 2) ^ 2 ≠ 0 := by
      rw [he2]
      exact hsq
    field_simp [hd', hsq']
    ring

private lemma t_limit : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private lemma exp_limit (c : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (c * t)) (𝓝[>] 0) (𝓝 1) := by
  simpa using (show ContinuousAt (fun t : ℝ => Real.exp (c * t)) 0 by
    fun_prop).tendsto.mono_left nhdsWithin_le_nhds

private lemma K_limit : Tendsto K (𝓝[>] 0) (𝓝 (K 0)) :=
  K_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private lemma log_recip_atTop :
    Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
  convert tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero using 1
  ext t
  simp [one_div, Real.log_inv, Function.comp_def]

private lemma inv_log_limit :
    Tendsto (fun t : ℝ => (Real.log (1 / t))⁻¹) (𝓝[>] 0) (𝓝 0) :=
  log_recip_atTop.inv_tendsto_atTop

private lemma log_argument_difference :
    Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-(2 * t))) + Real.log (1 / t))
      (𝓝[>] 0) (𝓝 (-Real.log (1 / 2))) := by
  have h := (Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp
    log_argument_ratio_limit
  apply h.neg.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hw : 0 < 1 - Real.exp (-(2 * t)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  change -Real.log (t / (1 - Real.exp (-(2 * t)))) = _
  rw [Real.log_div ht.ne' hw.ne', one_div, Real.log_inv]
  ring

private lemma D1_log_ratio :
    Tendsto (fun t : ℝ => (-D1 t) / Real.log (1 / t))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hb : Tendsto (fun t : ℝ => K t / 2 - Real.exp (t / 2) +
      Real.exp (-t / 2) * Real.log (2 * Real.pi)) (𝓝[>] 0)
      (𝓝 (K 0 / 2 - 1 + Real.log (2 * Real.pi))) := by
    convert ((K_limit.div_const 2).sub (exp_limit (1/2))).add
      ((exp_limit (-1/2)).mul_const (Real.log (2 * Real.pi))) using 1
    · funext t; ring_nf
    · norm_num
  have hl := log_argument_difference.mul inv_log_limit
  have hd : Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-(2 * t))) /
      Real.log (1 / t)) (𝓝[>] 0) (𝓝 (-1)) := by
    have hn : ∀ᶠ t : ℝ in 𝓝[>] 0, Real.log (1 / t) ≠ 0 :=
      (log_recip_atTop.eventually (eventually_gt_atTop 0)).mono (fun _ h => h.ne')
    have htmp := (hl.sub_const 1)
    have heq :
        (fun t : ℝ => (Real.log (1 - Real.exp (-(2 * t))) + Real.log (1 / t)) *
          (Real.log (1 / t))⁻¹ - 1) =ᶠ[𝓝[>] 0]
        (fun t => Real.log (1 - Real.exp (-(2 * t))) / Real.log (1 / t)) := by
      filter_upwards [hn] with t ht
      change (Real.log (1 - Real.exp (-(2 * t))) + Real.log (1 / t)) *
        (Real.log (1 / t))⁻¹ - 1 =
        Real.log (1 - Real.exp (-(2 * t))) / Real.log (1 / t)
      field_simp [ht]
      ring
    simpa using Filter.Tendsto.congr' heq htmp
  have hm := (hb.mul inv_log_limit).neg.sub
    (((exp_limit (-1/2)).div_const 2).mul hd)
  convert hm using 1
  · ext t; dsimp [D1]; ring_nf
  · norm_num

private lemma t_log_sq_limit :
    Tendsto (fun t : ℝ => t * Real.log (1 / t) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    tendsto_inv_nhdsGT_zero
  convert h using 1
  · ext t; simp [one_div, div_eq_mul_inv, mul_comm]

private lemma weighted_D1_sq :
    Tendsto (fun t : ℝ => t * D1 t ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hn : ∀ᶠ t : ℝ in 𝓝[>] 0, Real.log (1 / t) ≠ 0 :=
    (log_recip_atTop.eventually (eventually_gt_atTop 0)).mono (fun _ h => h.ne')
  have htmp := t_log_sq_limit.mul (D1_log_ratio.pow 2)
  have heq :
      (fun t : ℝ => t * Real.log (1 / t) ^ 2 * (-D1 t / Real.log (1 / t)) ^ 2) =ᶠ[𝓝[>] 0]
        (fun t => t * D1 t ^ 2) := by
    filter_upwards [hn] with t ht
    field_simp [ht]
  simpa using Filter.Tendsto.congr' heq htmp

private lemma weighted_D3 :
    Tendsto (fun t : ℝ => t ^ 2 * D3 t) (𝓝[>] 0) (𝓝 (-1 / 2)) := by
  have h1 := (t_limit.mul weighted_D1_limit).div_const 4
  have h2 := ((t_limit.pow 2).mul (exp_limit (1/2))).div_const 2
  have h3 := ((t_limit.mul (exp_limit (-1/2))).mul exp_ratio_limit).div_const 2
  have h4 := ((exp_limit (3/2)).mul (exp_ratio_limit.pow 2)).const_mul 2
  convert h1.sub h2 |>.sub h3 |>.sub h4 using 1
  · ext t
    dsimp [D3]
    have he : Real.exp (3 * t / 2) = Real.exp (-t / 2) * Real.exp (2 * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have htw : t * 2 = 2 * t := by ring
    by_cases hden : Real.exp (2 * t) - 1 = 0
    · simp [hden]
      ring
    · have hsq : 1 - 2 * Real.exp (2 * t) + Real.exp (2 * t) ^ 2 ≠ 0 := by
        nlinarith [sq_pos_of_ne_zero hden]
      have he2 : Real.exp (t * 2) = Real.exp (2 * t) := by congr 1 <;> ring
      have hden' : Real.exp (t * 2) - 1 ≠ 0 := by rw [he2]; exact hden
      have hsq' : 1 - 2 * Real.exp (t * 2) + Real.exp (t * 2) ^ 2 ≠ 0 := by
        rw [he2]
        exact hsq
      field_simp [hden', hsq']
      have he3 : Real.exp (t * 3 / 2) = Real.exp (t * 2) * Real.exp (-t / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he3]
      ring
  · norm_num

private lemma logK_curvature_limit :
    Tendsto (fun t : ℝ => t * (K t * D2 t - D1 t ^ 2))
      (𝓝[>] 0) (𝓝 (K 0 / 2)) := by
  convert (K_limit.mul weighted_D2_limit).sub weighted_D1_sq using 1
  · ext t; ring
  · ring

private lemma logh_curvature_limit :
    Tendsto (fun t : ℝ => t ^ 2 * ((-D1 t) * (-D3 t) - (-D2 t) ^ 2) /
      Real.log (1 / t)) (𝓝[>] 0) (𝓝 (1 / 4)) := by
  have h := (D1_log_ratio.mul weighted_D3.neg).sub
    ((weighted_D2_limit.pow 2).mul inv_log_limit)
  convert h using 1
  · ext t; ring
  · norm_num

private lemma log_strictConvex {f f' f'' : ℝ → ℝ} {δ : ℝ}
    (hd : ∀ t ∈ Ioo 0 δ, HasDerivAt f (f' t) t)
    (hdd : ∀ t ∈ Ioo 0 δ, HasDerivAt f' (f'' t) t)
    (hp : ∀ t ∈ Ioo 0 δ, 0 < f t)
    (hc : ∀ t ∈ Ioo 0 δ, 0 < f t * f'' t - f' t ^ 2) :
    StrictConvexOn ℝ (Ioo 0 δ) (fun t => Real.log (f t)) := by
  have hdlog (t : ℝ) (ht : t ∈ Ioo 0 δ) := (hd t ht).log (hp t ht).ne'
  have heq (t : ℝ) (ht : t ∈ Ioo 0 δ) :
      deriv (fun u => Real.log (f u)) t = f' t / f t := (hdlog t ht).deriv
  apply strictConvexOn_of_deriv2_pos (convex_Ioo 0 δ)
    (fun t ht => (hdlog t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' : t ∈ Ioo 0 δ := interior_subset ht
  have hquot := (hdd t ht').div (hd t ht') (hp t ht').ne'
  have hlocal : deriv (fun u => Real.log (f u)) =ᶠ[𝓝 t] (fun u => f' u / f u) := by
    filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with u hu using heq u hu
  have hder := hquot.congr_of_eventuallyEq hlocal
  change 0 < deriv (deriv (fun u => Real.log (f u))) t
  rw [hder.deriv]
  apply div_pos _ (sq_pos_of_pos (hp t ht'))
  nlinarith [hc t ht']

private lemma logK_strictConvex_closed {δ : ℝ} (hδ2 : δ < Real.log 2)
    (hp : ∀ t ∈ Icc 0 δ, 0 < K t)
    (hc : ∀ t ∈ Ioo 0 δ, 0 < K t*D2 t-D1 t^2) :
    StrictConvexOn ℝ (Icc 0 δ) (fun t => Real.log (K t)) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc 0 δ)
    (K_continuous.continuousOn.log (fun t ht => (hp t ht).ne'))
  intro t ht
  rw [interior_Icc] at ht
  have hKt := hasDerivAt_K ht.1 (ht.2.trans hδ2)
  have hD1t := hasDerivAt_D1 ht.1 (ht.2.trans hδ2)
  have hquot := hD1t.div hKt (hp t ⟨ht.1.le, ht.2.le⟩).ne'
  have hlocal : deriv (fun u => Real.log (K u)) =ᶠ[𝓝 t] (fun u => D1 u/K u) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact ((hasDerivAt_K hu.1 (hu.2.trans hδ2)).log (hp u ⟨hu.1.le, hu.2.le⟩).ne').deriv
  have hder := hquot.congr_of_eventuallyEq hlocal
  change 0 < deriv (deriv (fun u => Real.log (K u))) t
  rw [hder.deriv]
  apply div_pos _ (sq_pos_of_pos (hp t ⟨ht.1.le, ht.2.le⟩))
  nlinarith [hc t ht]

/-- A common actual arithmetic window controls both logarithmic curvatures and the cusp.
No assertion about a four-node inverse is packaged into this analytic supplier. -/
theorem exists_derivative_control_window : ∃ δ : ℝ,
    0 < δ ∧ δ < Real.log 2 ∧ δ ≤ Real.exp (-1) ∧
    (∀ t ∈ Ioc 0 δ,
      K 0 / 2 ≤ K t ∧ D1 t < 0 ∧
      1 / (4 * t) ≤ D2 t ∧ D2 t ≤ 1 / t ∧
      -D1 t ≤ Real.log (1 / t) ∧
      0 < K t * D2 t - D1 t ^ 2 ∧
      0 < (-D1 t) * (-D3 t) - (-D2 t) ^ 2) ∧
    (∀ t ∈ Ioo 0 δ, HasDerivAt D2 (D3 t) t) ∧
    StrictConvexOn ℝ (Icc 0 δ) (fun t => Real.log (K t)) ∧
    StrictConvexOn ℝ (Ioo 0 δ) (fun t => Real.log (-D1 t)) := by
  have hK := K_limit.eventually (Ioi_mem_nhds (show K 0 / 2 < K 0 by linarith [K_zero_pos]))
  have hD1 := D1_atBot.eventually (eventually_lt_atBot 0)
  have hD2 := weighted_D2_limit.eventually (Ioo_mem_nhds
    (by norm_num : (1/4 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1))
  have hh := D1_log_ratio.eventually (Iio_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hkc := logK_curvature_limit.eventually (Ioi_mem_nhds (by linarith [K_zero_pos] : 0 < K 0 / 2))
  have hhc := logh_curvature_limit.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1/4))
  have hlog : ∀ᶠ t : ℝ in 𝓝 0, t < Real.log 2 :=
    Iio_mem_nhds (Real.log_pos (by norm_num))
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t < Real.exp (-1) :=
    Iio_mem_nhds (Real.exp_pos (-1))
  have hwin : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t < Real.log 2 ∧ t < Real.exp (-1) ∧ 0 < Real.log (1/t) ∧
      K 0 / 2 < K t ∧ D1 t < 0 ∧
      (1/4 : ℝ) < t * D2 t ∧ t * D2 t < 1 ∧
      (-D1 t) / Real.log (1/t) < 1 ∧
      0 < t * (K t * D2 t - D1 t ^ 2) ∧
      0 < t^2 * ((-D1 t) * (-D3 t) - (-D2 t)^2) / Real.log (1/t) := by
    filter_upwards [hK, hD1, hD2, hh, hkc, hhc,
      hlog.filter_mono nhdsWithin_le_nhds,
      hsmall.filter_mono nhdsWithin_le_nhds,
      log_recip_atTop.eventually (eventually_gt_atTop 0)] with t hk hd1 hd2 hh hc hc' ht he hl
    exact ⟨ht, he, hl, hk, hd1, hd2.1, hd2.2, hh, hc, hc'⟩
  obtain ⟨δ, hδ, hall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hwin
  have hδall := hall ⟨hδ, le_rfl⟩
  have hbound (t : ℝ) (ht : t ∈ Ioc 0 δ) :
      K 0 / 2 ≤ K t ∧ D1 t < 0 ∧
      1 / (4*t) ≤ D2 t ∧ D2 t ≤ 1/t ∧
      -D1 t ≤ Real.log (1/t) ∧
      0 < K t * D2 t - D1 t ^ 2 ∧
      0 < (-D1 t)*(-D3 t)-(-D2 t)^2 := by
    rcases hall ht with ⟨_, _, hl, hk, hd1, hg, hg', hh, hc, hc'⟩
    refine ⟨hk.le, hd1, ?_, ?_, ?_, ?_, ?_⟩
    · apply (div_le_iff₀ (mul_pos (by norm_num) ht.1)).mpr
      nlinarith
    · exact (le_div_iff₀ ht.1).mpr (by nlinarith)
    · exact ((div_lt_one hl).mp hh).le
    · exact (mul_pos_iff_of_pos_left ht.1).mp hc
    · have hnum := (div_pos_iff_of_pos_right hl).mp hc'
      exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ht.1)).mp hnum
  refine ⟨δ, hδ, hδall.1, hδall.2.1.le, hbound,
    (fun t ht => hasDerivAt_D2 ht.1 (ht.2.trans hδall.1)), ?_, ?_⟩
  · apply logK_strictConvex_closed hδall.1
    · intro t ht
      rcases eq_or_lt_of_le ht.1 with hzero | hpos
      · simpa [← hzero] using K_zero_pos
      · exact (show 0 < K 0/2 by linarith [K_zero_pos]).trans_le (hbound t ⟨hpos, ht.2⟩).1
    · exact fun t ht => (hbound t ⟨ht.1, ht.2.le⟩).2.2.2.2.2.1
  · exact log_strictConvex
      (fun t ht => (hasDerivAt_D1 ht.1 (ht.2.trans hδall.1)).neg)
      (fun t ht => (hasDerivAt_D2 ht.1 (ht.2.trans hδall.1)).neg)
      (fun t ht => neg_pos.mpr (hbound t ⟨ht.1, ht.2.le⟩).2.1)
      (fun t ht => (hbound t ⟨ht.1, ht.2.le⟩).2.2.2.2.2.2)

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPrecision
