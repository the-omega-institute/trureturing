/- GID: D5/S3/Analytic/OriginalHalfBinomialEndpoint
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence]
   utility: none
   digest: Original period endpoint log16 and its nome quotient 1/16. -/

import D5.S3.Analytic.OriginalHalfBinomialIntegral
import D5.S3.Analytic.OriginalHalfBinomialPeriod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The complementary original period fixes the logarithmic endpoint and radial nome. -/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace D5.S3.Analytic.OriginalHalfBinomialEndpoint

private def F (r : ℝ) : ℝ := (OriginalHalfBinomialPeriod.period (r : ℂ)).re
private def A (r θ : ℝ) : ℝ := 1 / Real.sqrt (r + (1 - r) * Real.sin θ ^ 2)
private def B (r θ : ℝ) : ℝ := Real.cos θ / Real.sqrt (r + Real.sin θ ^ 2)
private def C (θ : ℝ) : ℝ := Real.sin θ / (1 + Real.cos θ)

private lemma angle_bounds {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin θ ∧ 0 ≤ Real.cos θ := by
  constructor
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

private lemma A_continuous {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : Continuous (A r) := by
  apply continuous_const.div
    ((continuous_const.add (continuous_const.mul (Real.continuous_sin.pow 2))).sqrt)
  intro θ
  apply ne_of_gt (Real.sqrt_pos.2 _)
  exact add_pos_of_pos_of_nonneg hr (mul_nonneg (by linarith) (sq_nonneg _))

private lemma B_continuous {r : ℝ} (hr : 0 < r) : Continuous (B r) := by
  apply Real.continuous_cos.div
    ((continuous_const.add (Real.continuous_sin.pow 2)).sqrt)
  intro θ
  exact ne_of_gt (Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg hr (sq_nonneg _)))

set_option maxHeartbeats 800000 in
private lemma residual_bounds {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 (Real.pi / 2)) : 0 ≤ A r θ - B r θ ∧ A r θ - B r θ ≤ 2 := by
  obtain ⟨hs, hc⟩ := angle_bounds hθ
  let s := Real.sin θ
  let c := Real.cos θ
  let u := Real.sqrt (r + (1 - r) * s ^ 2)
  let v := Real.sqrt (r + s ^ 2)
  have hs1 : s ≤ 1 := Real.sin_le_one θ
  have hc1 : c ≤ 1 := Real.cos_le_one θ
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have ha : 0 < r + (1 - r) * s ^ 2 :=
    add_pos_of_pos_of_nonneg hr (mul_nonneg (by linarith) (sq_nonneg _))
  have hb : 0 < r + s ^ 2 := add_pos_of_pos_of_nonneg hr (sq_nonneg _)
  have hu : 0 < u := Real.sqrt_pos.2 ha
  have hv : 0 < v := Real.sqrt_pos.2 hb
  have hu2 : u ^ 2 = r + (1 - r) * s ^ 2 := Real.sq_sqrt ha.le
  have hv2 : v ^ 2 = r + s ^ 2 := Real.sq_sqrt hb.le
  have huv : u ≤ v := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
  have hsu : s ≤ u := by nlinarith [Real.sin_sq_le_one θ]
  have hsv : s ≤ v := by nlinarith
  have hsc1 : 1 - c ≤ s := by nlinarith [mul_nonneg hs hc]
  have hs2u : s ^ 2 ≤ u := le_trans (by nlinarith) hsu
  have hrat : (v - u) * (v + u) = r * s ^ 2 := by nlinarith [hu2, hv2]
  have hprod : r * s ^ 2 ≤ u * v * (v + u) := by
    calc
      r * s ^ 2 ≤ r * u := mul_le_mul_of_nonneg_left hs2u hr.le
      _ ≤ v ^ 2 * u := by nlinarith
      _ ≤ u * v * (v + u) := by nlinarith [mul_nonneg (sq_nonneg u) hv.le]
  have hdiff : v - u ≤ u * v := by
    apply (mul_le_mul_iff_left₀ (by linarith : 0 < v + u)).mp
    rw [hrat]
    exact hprod
  have hnum0 : 0 ≤ v - c * u := by nlinarith
  have hnum2 : v - c * u ≤ 2 * (u * v) := by
    have h := mul_le_mul_of_nonneg_left (hsc1.trans hsv) hu.le
    nlinarith
  change 0 ≤ 1 / u - c / v ∧ 1 / u - c / v ≤ 2
  have heq : 1 / u - c / v = (v - c * u) / (u * v) := by field_simp
  rw [heq]
  exact ⟨div_nonneg hnum0 (mul_pos hu hv).le,
    (div_le_iff₀ (mul_pos hu hv)).2 hnum2⟩

private lemma residual_tendsto {θ : ℝ} (hθ : θ ∈ Ioc 0 (Real.pi / 2)) :
    Tendsto (fun r => A r θ - B r θ) (𝓝[>] 0) (𝓝 (C θ)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc := (angle_bounds ⟨hθ.1.le, hθ.2⟩).2
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hA : Tendsto (fun r => A r θ) (𝓝[>] 0) (𝓝 (1 / Real.sin θ)) := by
    have hd : Tendsto (fun r : ℝ => r + (1 - r) * Real.sin θ ^ 2)
        (𝓝[>] 0) (𝓝 (Real.sin θ ^ 2)) := by
      convert ht.add ((tendsto_const_nhds.sub ht).mul tendsto_const_nhds) using 1 <;> simp
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div
      hd.sqrt
      (by simpa [Real.sqrt_sq hs.le] using hs.ne')
    simpa [A, Pi.div_def, Real.sqrt_sq hs.le] using h
  have hB : Tendsto (fun r => B r θ) (𝓝[>] 0)
      (𝓝 (Real.cos θ / Real.sin θ)) := by
    have hd : Tendsto (fun r : ℝ => r + Real.sin θ ^ 2)
        (𝓝[>] 0) (𝓝 (Real.sin θ ^ 2)) := by
      convert ht.add tendsto_const_nhds using 1 <;> simp
    have h := (tendsto_const_nhds (x := Real.cos θ)).div
      hd.sqrt
      (by simpa [Real.sqrt_sq hs.le] using hs.ne')
    simpa [B, Pi.div_def, Real.sqrt_sq hs.le] using h
  have heq : 1 / Real.sin θ - Real.cos θ / Real.sin θ = C θ := by
    dsimp [C]
    field_simp [hs.ne', ne_of_gt (show 0 < 1 + Real.cos θ by linarith)]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simpa only [heq] using hA.sub hB

private lemma integral_C : (∫ θ in (0 : ℝ)..Real.pi / 2, C θ) = Real.log 2 := by
  have hc : ContinuousOn C (Icc 0 (Real.pi / 2)) := by
    apply Real.continuous_sin.continuousOn.div
      (continuous_const.add Real.continuous_cos).continuousOn
    intro θ hθ
    exact ne_of_gt (by linarith [(angle_bounds hθ).2] : 0 < 1 + Real.cos θ)
  have hd (θ : ℝ) (hθ : θ ∈ uIcc 0 (Real.pi / 2)) :
      HasDerivAt (fun θ => -Real.log (1 + Real.cos θ)) (C θ) θ := by
    rw [uIcc_of_le (by positivity)] at hθ
    have h := (((hasDerivAt_const θ (1 : ℝ)).add (Real.hasDerivAt_cos θ)).log
      (ne_of_gt (by linarith [(angle_bounds hθ).2] : 0 < 1 + Real.cos θ))).neg
    convert h using 1 <;> simp [C, neg_div]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc (by positivity))
  norm_num at hi
  exact hi

private lemma integral_B {r : ℝ} (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, B r θ) + Real.log r / 2 =
      Real.log (1 + Real.sqrt (1 + r)) := by
  let P := fun θ => Real.log (Real.sin θ + Real.sqrt (r + Real.sin θ ^ 2))
  have hd (θ : ℝ) (hθ : θ ∈ uIcc 0 (Real.pi / 2)) :
      HasDerivAt P (B r θ) θ := by
    rw [uIcc_of_le (by positivity)] at hθ
    have ha : 0 < r + Real.sin θ ^ 2 := add_pos_of_pos_of_nonneg hr (sq_nonneg _)
    have hu : 0 < Real.sqrt (r + Real.sin θ ^ 2) := Real.sqrt_pos.2 ha
    have hp : 0 < Real.sin θ + Real.sqrt (r + Real.sin θ ^ 2) :=
      add_pos_of_nonneg_of_pos (angle_bounds hθ).1 hu
    have h := ((Real.hasDerivAt_sin θ).add
      (((hasDerivAt_const θ r).add ((Real.hasDerivAt_sin θ).pow 2)).sqrt ha.ne')).log hp.ne'
    convert h using 1
    dsimp [B]
    field_simp
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((B_continuous hr).intervalIntegrable _ _)
  dsimp [P] at hi
  simp only [Real.sin_zero, Real.sin_pi_div_two, one_pow, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, zero_add, Real.log_sqrt hr.le] at hi
  rw [add_comm r 1] at hi
  linarith

private lemma residual_integral_tendsto :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..Real.pi / 2, A r θ - B r θ)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with r hr hr1
    exact ⟨hr, hr1⟩
  rw [← integral_C]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2 : ℝ))
  · filter_upwards [hev] with r hr
    exact ((A_continuous hr.1 hr.2).sub (B_continuous hr.1)).aestronglyMeasurable
  · filter_upwards [hev] with r hr
    apply Eventually.of_forall
    intro θ hθ
    rw [uIoc_of_le (by positivity)] at hθ
    obtain ⟨hl, hu⟩ := residual_bounds hr.1 hr.2 ⟨hθ.1.le, hθ.2⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl] using hu
  · exact intervalIntegrable_const
  · apply Eventually.of_forall
    intro θ hθ
    rw [uIoc_of_le (by positivity)] at hθ
    exact residual_tendsto hθ

private lemma complementary_integral {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.pi * F (1 - r) = 2 * ∫ θ in (0 : ℝ)..Real.pi / 2, A r θ := by
  have he := (OriginalHalfBinomialIntegral.original_series_eq_integral (1 - r)
    (by linarith) (by linarith)).2.2
  have hf : F (1 - r) = (2 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi / 2,
      1 / Real.sqrt (1 - (1 - r) * Real.sin θ ^ 2)) := by
    exact congrArg Complex.re he
  have href := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => 1 / Real.sqrt (1 - (1 - r) * Real.sin θ ^ 2))
    (a := (0 : ℝ)) (b := Real.pi / 2) (Real.pi / 2)
  simp only [sub_self, sub_zero] at href
  have ha : (∫ θ in (0 : ℝ)..Real.pi / 2,
      1 / Real.sqrt (1 - (1 - r) * Real.sin (Real.pi / 2 - θ) ^ 2)) =
      ∫ θ in (0 : ℝ)..Real.pi / 2, A r θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [Real.sin_pi_div_two_sub]
    dsimp [A]
    congr 2
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [ha] at href
  rw [hf, ← href]
  field_simp

/-- The complementary literal period has logarithmic constant log(16). -/
theorem original_period_log16 :
    Tendsto (fun r : ℝ => Real.pi *
      (OriginalHalfBinomialPeriod.period ((1 - r : ℝ) : ℂ)).re + Real.log r)
      (𝓝[>] 0) (𝓝 (Real.log 16)) := by
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hj : Tendsto (fun r : ℝ => Real.log (1 + Real.sqrt (1 + r)))
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have h := (tendsto_const_nhds.add (tendsto_const_nhds.add ht).sqrt).log
      (by norm_num : (1 : ℝ) + Real.sqrt (1 + 0) ≠ 0)
    convert h using 1 <;> norm_num
  have hsum := (residual_integral_tendsto.add hj).const_mul 2
  have hc : 2 * (Real.log 2 + Real.log 2) = Real.log (16 : ℝ) := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    linarith
  rw [hc] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  have hB := integral_B hr
  have hA := complementary_integral hr hr1
  rw [intervalIntegral.integral_sub ((A_continuous hr hr1).intervalIntegrable _ _)
    ((B_continuous hr).intervalIntegrable _ _)]
  change 2 * ((∫ θ in (0 : ℝ)..Real.pi / 2, A r θ) -
    (∫ θ in (0 : ℝ)..Real.pi / 2, B r θ) + Real.log (1 + Real.sqrt (1 + r))) =
    Real.pi * F (1 - r) + Real.log r
  linarith

private lemma F_zero : F 0 = 1 := by
  have h := (OriginalHalfBinomialIntegral.original_series_eq_integral 0
    (by norm_num) (by norm_num)).2.2
  simpa [F, OriginalHalfBinomialPeriod.period, Real.pi_ne_zero] using congrArg Complex.re h

private lemma F_hasDerivAt_zero :
    HasDerivAt F (deriv OriginalHalfBinomialPeriod.period 0).re 0 := by
  exact (OriginalHalfBinomialPeriod.picard_fuchs (z := 0) (by norm_num)).1.hasDerivAt.real_of_complex

/-- For q=exp(pi*i*tau), the literal real radial nome satisfies q(r)/r -> 1/16. -/
theorem original_nome_quotient :
    Tendsto (fun r : ℝ => Real.exp (-Real.pi *
      (OriginalHalfBinomialPeriod.period ((1 - r : ℝ) : ℂ)).re /
      (OriginalHalfBinomialPeriod.period (r : ℂ)).re) / r)
      (𝓝[>] 0) (𝓝 (1 / 16)) := by
  have hF : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    simpa only [F_zero] using F_hasDerivAt_zero.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hinv := F_hasDerivAt_zero.inv (by rw [F_zero]; norm_num)
  have hslope : Tendsto (fun r : ℝ => (1 / F r - 1) / r) (𝓝[>] 0)
      (𝓝 (-((deriv OriginalHalfBinomialPeriod.period 0).re))) := by
    simpa [F_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hinv.tendsto_slope_zero_right
  have hlog : Tendsto (fun r : ℝ => Real.log r * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1))
  have hcorrection : Tendsto (fun r : ℝ => Real.log r * (1 / F r - 1))
      (𝓝[>] 0) (𝓝 0) := by
    have h := hlog.mul hslope
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    field_simp [ne_of_gt hr0]
  have he : Tendsto (fun r : ℝ => -Real.pi * F (1 - r) / F r - Real.log r)
      (𝓝[>] 0) (𝓝 (-Real.log 16)) := by
    have h := (original_period_log16.neg.div hF (by norm_num)).add hcorrection
    simp only [div_one, add_zero] at h
    apply h.congr'
    filter_upwards [] with r
    dsimp [F] at *
    ring
  have h := Real.continuous_exp.continuousAt.tendsto.comp he
  have hv : Real.exp (-Real.log (16 : ℝ)) = 1 / 16 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [hv] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change Real.exp (-Real.pi * F (1 - r) / F r - Real.log r) =
    Real.exp (-Real.pi * F (1 - r) / F r) / r
  rw [Real.exp_sub, Real.exp_log hr]

end D5.S3.Analytic.OriginalHalfBinomialEndpoint
