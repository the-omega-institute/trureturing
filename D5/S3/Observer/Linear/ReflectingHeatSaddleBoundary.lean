/- GID: D5/S3/Observer/Linear/ReflectingHeatSaddleBoundary
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatSaddleBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatSaddleDensity]
   utility: none
   digest: The reflecting heat saddle potential on the real boundary. -/

import D5.S3.Observer.Linear.ReflectingHeatSaddleDensity
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-! The reflecting heat saddle potential on the real boundary. -/

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open D5.S3.Analytic.Hardy.FiniteStripMomentBound (radius)
open EqualMassBins

private theorem exists_outer_root (c : ℂ) : ∃ z : ℂ, z ≠ 0 ∧ z + z⁻¹ = c ∧ 1 ≤ ‖z‖ := by
  obtain ⟨w, hw⟩ := Complex.cos_surjective (c / 2)
  let z := Complex.exp (w * Complex.I)
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

open Polynomial in
private theorem angularGreen_eq_log_outer_radius (ω : ℝ) {z : ℂ} (hz : z ≠ 0)
    (hroot : z + z⁻¹ = (ω : ℂ) * Complex.I - 2) (hz₁ : 1 ≤ ‖z‖) :
    spectralAverage (fun r => Real.log ‖(r : ℂ) - (ω : ℂ) * Complex.I‖) = Real.log ‖z‖ ∧
      IntervalIntegrable (fun θ => Real.log ‖Complex.ofReal (2 - 2 * Real.cos θ) -
        (ω : ℂ) * Complex.I‖) volume 0 Real.pi := by
  let p : ℂ[X] := (X - C z) * (X - C z⁻¹)
  let f (θ : ℝ) := Real.log ‖(Complex.ofReal (2 - 2 * Real.cos θ)) - (ω : ℂ) * Complex.I‖
  have hp : p ≠ 0 := by
    apply mul_ne_zero <;> exact X_sub_C_ne_zero _
  have hn : Real.posLog ‖z⁻¹‖ = 0 := by
    apply (Real.posLog_eq_zero_iff _).2
    rw [abs_of_nonneg (norm_nonneg _), norm_inv]
    exact inv_le_one_of_one_le₀ hz₁
  have hmah : p.logMahlerMeasure = Real.log ‖z‖ := by
    rw [show p = (X - C z) * (X - C z⁻¹) from rfl,
      logMahlerMeasure_mul_eq_add_logMahlerMeasure hp, logMahlerMeasure_X_sub_C,
      logMahlerMeasure_X_sub_C, hn, add_zero, Real.posLog_eq_log]
    rwa [abs_of_nonneg (norm_nonneg _)]
  have hval (θ : ℝ) : Real.log ‖p.eval (circleMap 0 (-1) θ)‖ = f θ := by
    let w := circleMap 0 (-1) θ
    have hw : ‖w‖ = 1 := by simp [w]
    have hwn : w ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simp [hw]
    have hsum : w + w⁻¹ = -2 * (Real.cos θ : ℂ) := by
      simp only [w, circleMap_zero, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
        inv_neg, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
      ring
    have he : p.eval w = w * (w + w⁻¹ - ((ω : ℂ) * Complex.I - 2)) := by
      simp only [p, eval_mul, eval_sub, eval_X, eval_C]
      rw [← hroot]
      field_simp [hz, hwn]
      ring
    change Real.log ‖p.eval w‖ = _
    rw [he, norm_mul, hw, one_mul, hsum]
    congr 2
    push_cast
    ring
  have hI : IntervalIntegrable f volume 0 (2 * Real.pi) := by
    have hi := p.intervalIntegrable_mahlerMeasure
    have hneg : IntervalIntegrable (fun θ => Real.log ‖p.eval (circleMap 0 (-1) θ)‖)
        volume 0 (2 * Real.pi) := by
      let g (v : ℂ) := Real.log ‖p.eval v‖
      have hi' : CircleIntegrable g 0 1 := hi
      have hn' : CircleIntegrable g 0 (-1) := by simpa only [circleIntegrable_neg_radius] using hi'
      exact hn'
    simpa only [hval] using hneg
  have hsymm (θ : ℝ) : f (2 * Real.pi - θ) = f θ := by
    dsimp only [f]
    rw [Real.cos_two_pi_sub]
  have hmid : Real.pi ∈ uIcc 0 (2 * Real.pi) := by
    rw [uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have h₁ : IntervalIntegrable f volume 0 Real.pi :=
    hI.mono_set (uIcc_subset_uIcc_left hmid)
  have h₂ : IntervalIntegrable f volume Real.pi (2 * Real.pi) :=
    hI.mono_set (uIcc_subset_uIcc_right hmid)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have hreflect : (∫ θ in Real.pi..2 * Real.pi, f θ) = ∫ θ in 0..Real.pi, f θ := by
    have he := intervalIntegral.integral_comp_sub_left f (a := 0) (b := Real.pi) (2 * Real.pi)
    rw [sub_zero, show 2 * Real.pi - Real.pi = Real.pi by ring] at he
    simp only [hsymm] at he
    exact he.symm
  have havg : p.logMahlerMeasure = (∫ θ in 0..Real.pi, f θ) / Real.pi := by
    rw [logMahlerMeasure_def, ← Real.circleAverage_neg_radius, Real.circleAverage_def]
    simp only [hval, smul_eq_mul]
    rw [← hsplit, hreflect]
    ring
  exact ⟨havg.symm.trans hmah, h₁⟩

/-- The value of the saddle square root on the real boundary. -/
def realSaddleRoot (β x : ℝ) : ℂ :=
  if x ≤ β then Complex.ofReal (Real.sqrt (β ^ 2 - x ^ 2))
  else Complex.ofReal (Real.sqrt (x ^ 2 - β ^ 2)) * Complex.I

private def potentialRatio (β t : ℝ) (w : ℂ) : ℂ :=
  1 + (w ^ 2 - (β : ℂ) ^ 2) / (t : ℂ) ^ 2

private theorem potentialRatio_slit {β t : ℝ} (hβ : 0 < β) (ht : β ≤ t)
    {w : ℂ} (hw : 0 < w.re) : potentialRatio β t w ∈ Complex.slitPlane := by
  have ht0 := hβ.trans_le ht
  have hs : 0 ≤ t ^ 2 - β ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hβ.le ht 2)
  rw [Complex.mem_slitPlane_iff]
  unfold potentialRatio
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
  by_cases hi : w.im = 0
  · left
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofReal_re,
      Complex.sub_re, Complex.ofReal_re, pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    have h : -1 < (w.re * w.re - β * β) / (t * t) := by
      rw [lt_div_iff₀ (mul_pos ht0 ht0)]
      nlinarith [sq_pos_of_pos hw]
    linarith
  · right
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.div_ofReal_im,
      Complex.sub_im, Complex.ofReal_im, sub_zero, pow_two, Complex.mul_im]
    rw [show w.re * w.im + w.im * w.re = 2 * (w.re * w.im) by ring]
    exact div_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hw.ne' hi))
      (mul_ne_zero ht0.ne' ht0.ne')

private theorem potentialDenominator_lower {β t δ : ℝ} (hβ : 0 < β) (ht : β ≤ t)
    {w : ℂ} (hδ : 0 ≤ δ) (hw : δ ≤ w.re) :
    δ ^ 2 ≤ ‖(t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2‖ := by
  let u := Real.sqrt (t ^ 2 - β ^ 2)
  have hu : u ^ 2 = t ^ 2 - β ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hβ.le ht 2))
  have he : (w + (u : ℂ) * Complex.I) * (w - (u : ℂ) * Complex.I) =
      (t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2 := by
    rw [show (w + (u : ℂ) * Complex.I) * (w - (u : ℂ) * Complex.I) =
      w ^ 2 - (u : ℂ) ^ 2 * Complex.I ^ 2 by ring, Complex.I_sq, ← Complex.ofReal_pow, hu]
    push_cast
    ring
  have h₁ : δ ≤ ‖w + (u : ℂ) * Complex.I‖ := hw.trans (by
    simpa [Complex.add_re, Complex.mul_re] using Complex.re_le_norm (w + (u : ℂ) * Complex.I))
  have h₂ : δ ≤ ‖w - (u : ℂ) * Complex.I‖ := hw.trans (by
    simpa [Complex.sub_re, Complex.mul_re] using Complex.re_le_norm (w - (u : ℂ) * Complex.I))
  rw [← he, norm_mul, pow_two]
  exact mul_le_mul h₁ h₂ hδ (norm_nonneg _)

private theorem hasDerivAt_potentialKernel {β t : ℝ} (hβ : 0 < β) (ht : β ≤ t)
    {w : ℂ} (hw : 0 < w.re) (d : ℝ) :
    HasDerivAt (fun v => Complex.log (potentialRatio β t v) * (d : ℂ))
      (2 * w / ((t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2) * (d : ℂ)) w := by
  have ht0 := hβ.trans_le ht
  have hratio := potentialRatio_slit hβ ht hw
  have h := (Complex.hasDerivAt_log hratio).comp w
    ((((hasDerivAt_pow 2 w).sub_const ((β : ℂ) ^ 2)).div_const ((t : ℂ) ^ 2)).const_add 1)
  convert h.mul_const (d : ℂ) using 1
  · simp [potentialRatio]
  · have hden : (t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2 ≠ 0 :=
      norm_pos_iff.mp ((sq_pos_of_pos hw).trans_le
        (potentialDenominator_lower hβ ht hw.le le_rfl))
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have he : potentialRatio β t w =
        ((t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2) / (t : ℂ) ^ 2 := by
      unfold potentialRatio
      field_simp [ht']
      ring
    rw [he]
    norm_num
    field_simp [ht', hden] <;> norm_num

private theorem potentialKernel_deriv_bound {β t δ B d D : ℝ} (hβ : 0 < β) (ht : β ≤ t)
    {w : ℂ} (hδ : 0 < δ) (hw : δ ≤ w.re) (hB : ‖w‖ ≤ B) (hd : 0 ≤ d ∧ d ≤ D) :
    ‖2 * w / ((t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2) * (d : ℂ)‖ ≤
      (2 * B * (1 + (B ^ 2 + β ^ 2) / δ ^ 2) * D) * (t ^ 2)⁻¹ := by
  let v : ℂ := (t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2
  have hB0 := (norm_nonneg w).trans hB
  have hv : δ ^ 2 ≤ ‖v‖ := potentialDenominator_lower hβ ht hδ.le hw
  have hv0 := (sq_pos_of_pos hδ).trans_le hv
  have ht0 := hβ.trans_le ht
  have htri : t ^ 2 ≤ ‖v‖ + (B ^ 2 + β ^ 2) := by
    calc
      t ^ 2 = ‖v + ((β : ℂ) ^ 2 - w ^ 2)‖ := by
        rw [show v + ((β : ℂ) ^ 2 - w ^ 2) = (t : ℂ) ^ 2 by dsimp [v]; ring]
        rw [norm_pow, Complex.norm_of_nonneg ht0.le]
      _ ≤ ‖v‖ + (‖(β : ℂ) ^ 2‖ + ‖w ^ 2‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ ≤ _ := by
        simp only [norm_pow, Complex.norm_of_nonneg hβ.le]
        linarith [pow_le_pow_left₀ (norm_nonneg w) hB 2]
  have hdiv : (t ^ 2) / ‖v‖ ≤ 1 + (B ^ 2 + β ^ 2) / δ ^ 2 := by
    calc
      _ ≤ (‖v‖ + (B ^ 2 + β ^ 2)) / ‖v‖ := div_le_div_of_nonneg_right htri hv0.le
      _ = 1 + (B ^ 2 + β ^ 2) / ‖v‖ := by rw [add_div, div_self hv0.ne']
      _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left (sq_nonneg B |>.trans (le_add_of_nonneg_right (sq_nonneg β))) (sq_pos_of_pos hδ) hv) _
  have hscale : ‖v‖⁻¹ ≤ (1 + (B ^ 2 + β ^ 2) / δ ^ 2) * (t ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos ht0)]
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  change ‖2 * w / v * (d : ℂ)‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, Complex.norm_of_nonneg hd.1, Complex.norm_ofNat,
    div_eq_mul_inv]
  calc
    _ ≤ (2 * B * ((1 + (B ^ 2 + β ^ 2) / δ ^ 2) * (t ^ 2)⁻¹)) * D := by
      have hM : 0 ≤ 2 * B := by positivity
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num))
        hscale (by positivity) hM) hd.2 hd.1 (by positivity)
    _ = _ := by ring

private def holomorphicPotential (β : ℝ) (density : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioi β, Complex.log (potentialRatio β t w) * (density t : ℂ)

private theorem holomorphicPotential_integrable_and_differentiable {β D : ℝ} {density : ℝ → ℝ}
    (hβ : 0 < β) (hc : ContinuousOn density (Ici β))
    (hd : ∀ t ∈ Ici β, 0 ≤ density t ∧ density t ≤ D) :
    ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun t => Complex.log (potentialRatio β t w) * (density t : ℂ)) (Ioi β) ∧
      DifferentiableAt ℂ (holomorphicPotential β density) w := by
  let F (w : ℂ) (t : ℝ) := Complex.log (potentialRatio β t w) * (density t : ℂ)
  let F' (w : ℂ) (t : ℝ) := 2 * w / ((t : ℂ) ^ 2 - (β : ℂ) ^ 2 + w ^ 2) * (density t : ℂ)
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF (w : ℂ) (hw : 0 < w.re) : ContinuousOn (F w) (Ioi β) := by
    apply ContinuousOn.mul _ (Complex.continuous_ofReal.comp_continuousOn
      (hc.mono Ioi_subset_Ici_self))
    apply ContinuousOn.clog
    · unfold potentialRatio
      apply continuousOn_const.add
      exact continuousOn_const.div (by fun_prop) (fun t ht =>
        pow_ne_zero _ (by exact_mod_cast (hβ.trans ht).ne'))
    · exact fun t ht => potentialRatio_slit hβ ht.le hw
  have hF' (w : ℂ) (hw : 0 < w.re) : ContinuousOn (F' w) (Ioi β) := by
    apply ContinuousOn.mul _ (Complex.continuous_ofReal.comp_continuousOn
      (hc.mono Ioi_subset_Ici_self))
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact norm_pos_iff.mp ((sq_pos_of_pos hw).trans_le
      (potentialDenominator_lower hβ ht.le hw.le le_rfl))
  intro w hw
  let δ := min β w.re / 2
  let B := max β ‖w‖ + 1
  let K := 2 * B * (1 + (B ^ 2 + β ^ 2) / δ ^ 2) * D
  let U : Set ℂ := {v | δ ≤ v.re} ∩ Metric.closedBall 0 B
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hU : Convex ℝ U := (convex_halfSpace_re_ge δ).inter
    (convex_closedBall 0 B)
  have hβmem : (β : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · change δ ≤ β
      dsimp [δ]
      linarith [min_le_left β w.re]
    · simp [B, dist_zero_right, abs_of_pos hβ]
      linarith [le_max_left β ‖w‖]
  have hU_nhds : U ∈ 𝓝 w := by
    apply inter_mem
    · have hstrict : IsOpen {v : ℂ | δ < v.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hwd : w ∈ {v : ℂ | δ < v.re} := by
        change δ < w.re
        dsimp [δ]
        linarith [min_le_right β w.re]
      exact mem_of_superset (hstrict.mem_nhds hwd) (fun v hv => (show δ < v.re from hv).le)
    · apply Metric.closedBall_mem_nhds_of_mem
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [B]
      linarith [le_max_right β ‖w‖]
  have hwmem := mem_of_mem_nhds hU_nhds
  have hbound (t : ℝ) (ht : β < t) (v : ℂ) (hv : v ∈ U) : ‖F' v t‖ ≤ K * (t ^ 2)⁻¹ :=
    potentialKernel_deriv_bound hβ ht.le hδ hv.1
      (by simpa [dist_zero_right] using hv.2) (hd t ht.le)
  have hderiv (t : ℝ) (ht : β < t) (v : ℂ) (hv : v ∈ U) :
      HasDerivAt (F · t) (F' v t) v := hasDerivAt_potentialKernel hβ ht.le (hδ.trans_le hv.1) _
  have hmeas := (hF w hw).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hint : IntegrableOn (F w) (Ioi β) := by
    apply ((integrableOn_inv_sq hβ).const_mul (K * ‖w - (β : ℂ)‖)).mono' hmeas
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β))] with t ht
    have h := hU.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => (hderiv t ht v hv).hasDerivWithinAt) (hbound t ht) hβmem hwmem
    have hz : F (β : ℂ) t = 0 := by simp [F, potentialRatio]
    rw [hz, sub_zero] at h
    exact h.trans_eq (by ring)
  refine ⟨hint, ?_⟩
  have hw' : w ∈ {v : ℂ | 0 < v.re} := hw
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU_nhds
    (Filter.Eventually.mono (hopen.mem_nhds hw') fun v hv =>
      (hF v hv).aestronglyMeasurable measurableSet_Ioi)
    hint ((hF' w hw).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β))).mono hbound)
    ((integrableOn_inv_sq hβ).const_mul K)
    ((ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := β))).mono hderiv)).2.differentiableAt

private def complexSaddleLogAverage (β : ℝ) (w : ℂ) : ℂ :=
  (∫ θ in 0..Real.pi,
    Complex.log (w + (radius β (2 - 2 * Real.cos θ) : ℂ))) / (Real.pi : ℂ)

private theorem continuous_complexSaddleLogKernel {β : ℝ} (hβ : 0 < β)
    {w : ℂ} (hw : 0 ≤ w.re) :
    Continuous (fun θ => Complex.log (w + (radius β (2 - 2 * Real.cos θ) : ℂ))) := by
  apply Continuous.clog (by unfold radius; fun_prop)
  intro θ
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.add_re, Complex.ofReal_re]
  have hp : 0 < radius β (2 - 2 * Real.cos θ) := by unfold radius; positivity
  linarith

private theorem complexSaddleLogAverage_analytic {β : ℝ} (hβ : 0 < β) :
    AnalyticOnNhd ℂ (complexSaddleLogAverage β) {w | 0 < w.re} := by
  let R (θ : ℝ) := radius β (2 - 2 * Real.cos θ)
  let F (w : ℂ) (θ : ℝ) := Complex.log (w + (R θ : ℂ))
  let F' (w : ℂ) (θ : ℝ) := (w + (R θ : ℂ))⁻¹
  let U : Set ℂ := {w | 0 < w.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hR (θ : ℝ) : β ≤ R θ := by
    unfold R radius
    exact (Real.le_sqrt hβ.le (by positivity)).2 (by linarith [sq_nonneg (2 - 2 * Real.cos θ)])
  have hre (w : ℂ) (hw : w ∈ U) (θ : ℝ) : β ≤ (w + (R θ : ℂ)).re := by
    change 0 < w.re at hw
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hR θ]
  have hne (w : ℂ) (hw : w ∈ U) (θ : ℝ) : w + (R θ : ℂ) ≠ 0 :=
    norm_pos_iff.mp (hβ.trans_le ((hre w hw θ).trans (Complex.re_le_norm _)))
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (F w) :=
    continuous_complexSaddleLogKernel hβ (le_of_lt hw)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (F' w) :=
    Continuous.inv₀ (by unfold R radius; fun_prop) (hne w hw)
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro w hw
  let μ := volume.restrict (Ioc (0 : ℝ) Real.pi)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (hopen.mem_nhds hw) (Filter.Eventually.mono (hopen.mem_nhds hw) fun v hv => (hc v hv).aestronglyMeasurable)
    ((hc w hw).intervalIntegrable (μ := volume) 0 Real.pi).1
    ((hc' w hw).aestronglyMeasurable)
    (ae_of_all μ fun θ v hv => by
      rw [show F' v θ = (v + (R θ : ℂ))⁻¹ from rfl, norm_inv]
      exact inv_anti₀ hβ ((hre v hv θ).trans (Complex.re_le_norm _)))
    (integrable_const β⁻¹)
    (ae_of_all μ fun θ v hv => by
      simpa only [F, F', Function.comp_def, id_eq, mul_one] using (Complex.hasDerivAt_log
        (Complex.mem_slitPlane_iff.mpr (Or.inl (hβ.trans_le (hre v hv θ))))).comp v
          ((hasDerivAt_id v).add_const (R θ : ℂ)))).2
  have h := (hd.div_const (Real.pi : ℂ)).differentiableAt.differentiableWithinAt (s := U)
  have he : complexSaddleLogAverage β = fun v => (∫ θ, F v θ ∂μ) / (Real.pi : ℂ) := by
    funext v
    unfold complexSaddleLogAverage
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [he]
  exact h

private theorem complexSaddleLogAverage_re {β : ℝ} (hβ : 0 < β)
    {w : ℂ} (hw : 0 ≤ w.re) :
    (complexSaddleLogAverage β w).re =
      spectralAverage (fun r => Real.log ‖w + (radius β r : ℂ)‖) := by
  let f (θ : ℝ) := Complex.log (w + (radius β (2 - 2 * Real.cos θ) : ℂ))
  have hi : IntervalIntegrable f volume 0 Real.pi :=
    (continuous_complexSaddleLogKernel hβ hw).intervalIntegrable _ _
  have h := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ θ in 0..Real.pi, (f θ).re) = (∫ θ in 0..Real.pi, f θ).re at h
  simp only [complexSaddleLogAverage, Complex.div_ofReal_re, spectralAverage]
  change (∫ θ in 0..Real.pi, f θ).re / Real.pi = _
  rw [← h]
  simp only [f, Complex.log_re]

private theorem complexSaddleLogAverage_real_argument {β u : ℝ}
    (hu : 0 ≤ u) :
    complexSaddleLogAverage β (u : ℂ) =
      (spectralAverage (fun r => Real.log (u + radius β r)) : ℂ) := by
  unfold complexSaddleLogAverage spectralAverage
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [← Complex.ofReal_add, ← Complex.ofReal_log
    (add_nonneg hu (show 0 ≤ radius β (2 - 2 * Real.cos θ) from Real.sqrt_nonneg _))]

private theorem holomorphicPotential_eval (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2) :
    Set.EqOn (holomorphicPotential β (saddleDensity n β))
      (fun w => (n : ℂ) * (((a : ℂ) / 2) * (w - (β : ℂ)) -
        complexSaddleLogAverage β w + (saddleLogAverage β 0 : ℂ)))
      {w | 0 < w.re} := by
  obtain ⟨hc, hcap, _, _⟩ := saddleDensity_spec n hn ha hβ hs
  let F := holomorphicPotential β (saddleDensity n β)
  let G (w : ℂ) := (n : ℂ) * (((a : ℂ) / 2) * (w - (β : ℂ)) -
        complexSaddleLogAverage β w + (saddleLogAverage β 0 : ℂ))
  let U : Set ℂ := {w | 0 < w.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    exact fun w hw => ((holomorphicPotential_integrable_and_differentiable hβ hc hcap w hw).2).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U :=
    analyticOnNhd_const.mul
      (((analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const)).sub
        (complexSaddleLogAverage_analytic hβ)).add analyticOnNhd_const)
  have hU : IsPreconnected U :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hreal (u : ℝ) (hu : β ≤ u) : F (u : ℂ) = G (u : ℂ) := by
    let y := Real.sqrt (u ^ 2 - β ^ 2)
    have hy₂ : y ^ 2 = u ^ 2 - β ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hβ.le hu 2))
    have hRu : radius β y = u := by
      rw [radius, hy₂, sub_add_cancel, Real.sqrt_sq (hβ.le.trans hu)]
    have hR0 : radius β 0 = β := by simp [radius, Real.sqrt_sq hβ.le]
    have hImag := imaginaryPotential_eval_at_saddle n hn ha hβ hs y (Real.sqrt_nonneg _)
    have hval : F (u : ℂ) = (imaginaryPotential β (saddleDensity n β) y : ℂ) := by
      unfold F holomorphicPotential imaginaryPotential
      rw [← integral_complex_ofReal (μ := volume.restrict (Ioi β))
        (f := fun t => Real.log (1 + y ^ 2 / t ^ 2) * saddleDensity n β t)]
      apply integral_congr_ae
      filter_upwards with t
      have hpos : 0 ≤ 1 + y ^ 2 / t ^ 2 := by positivity
      rw [potentialRatio, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
        ← Complex.ofReal_sub, ← hy₂, ← Complex.ofReal_div, ← Complex.ofReal_one,
        ← Complex.ofReal_add, ← Complex.ofReal_log hpos, ← Complex.ofReal_mul]
    rw [hval, hImag]
    unfold G
    rw [complexSaddleLogAverage_real_argument (hβ.le.trans hu)]
    simp only [saddleLogAverage, hRu]
    push_cast
    ring
  apply hF.eqOn_of_preconnected_of_mem_closure hG hU
    (show (β : ℂ) ∈ U from hβ)
  have hcβ : β ∈ closure (Ioi β) := by rw [closure_Ioi]; exact mem_Ici.mpr le_rfl
  refine closure_mono ?_ (image_closure_subset_closure_image Complex.continuous_ofReal
    (mem_image_of_mem Complex.ofReal hcβ))
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨hreal u hu.le, by simpa using hu.ne'⟩

private theorem realSaddleRoot_spec {β x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) :
    0 ≤ (realSaddleRoot β x).re ∧ (realSaddleRoot β x) ^ 2 =
      ((β ^ 2 - x ^ 2 : ℝ) : ℂ) := by
  by_cases h : x ≤ β
  · have hs := Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hx h 2))
    simp only [realSaddleRoot, if_pos h, Complex.ofReal_re, ← Complex.ofReal_pow, hs]
    exact ⟨Real.sqrt_nonneg _, trivial⟩
  · have hs := Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hβ.le (le_of_not_ge h) 2))
    simp only [realSaddleRoot, if_neg h, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, le_refl, true_and,
      mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hs]
    push_cast
    ring

private theorem potentialRatio_boundary {β x t : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) :
    potentialRatio β t (realSaddleRoot β x) = ((1 - x ^ 2 / t ^ 2 : ℝ) : ℂ) := by
  rw [potentialRatio, (realSaddleRoot_spec hβ hx).2]
  push_cast
  ring

private theorem potentialRatio_norm_mono_real {β t : ℝ} (hβ : 0 < β) (ht : β ≤ t)
    {w : ℂ} (hw : 0 ≤ w.re) {e : ℝ} (he : 0 ≤ e) :
    ‖potentialRatio β t w‖ ≤ ‖potentialRatio β t (w + (e : ℂ))‖ := by
  let u := Real.sqrt (t ^ 2 - β ^ 2)
  have hu : u ^ 2 = t ^ 2 - β ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hβ.le ht 2))
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (hβ.trans_le ht).ne'
  have hf (z : ℂ) : potentialRatio β t z =
      (z + (u : ℂ) * Complex.I) * (z - (u : ℂ) * Complex.I) / (t : ℂ) ^ 2 := by
    rw [show (z + (u : ℂ) * Complex.I) * (z - (u : ℂ) * Complex.I) =
      z ^ 2 - (u : ℂ) ^ 2 * Complex.I ^ 2 by ring, Complex.I_sq, ← Complex.ofReal_pow, hu]
    unfold potentialRatio
    push_cast
    field_simp [ht0]
    ring
  have hm (z : ℂ) (hz : 0 ≤ z.re) : ‖z‖ ≤ ‖z + (e : ℂ)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith [mul_nonneg hz he, sq_nonneg e]
  rw [hf, hf, norm_div, norm_div, norm_mul, norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
  · simpa [add_right_comm] using hm (w + (u : ℂ) * Complex.I)
      (by simpa [Complex.add_re, Complex.mul_re] using hw)
  · simpa [add_sub_right_comm] using hm (w - (u : ℂ) * Complex.I)
      (by simpa [Complex.sub_re, Complex.mul_re] using hw)

private theorem realPotential_boundary_limit {β D x : ℝ} {density : ℝ → ℝ}
    (hβ : 0 < β) (hx : 0 ≤ x) (bins : EqualMassBins β density)
    (hd : ∀ t ∈ Ici β, 0 ≤ density t ∧ density t ≤ D) :
    Tendsto (fun e : ℝ => (holomorphicPotential β density (realSaddleRoot β x + (e : ℂ))).re)
      (𝓝[>] 0) (𝓝 (realPotential β density x)) := by
  let S := realSaddleRoot β x
  let U (e : ℝ) := S + (e : ℂ)
  let F (e t : ℝ) := Real.log ‖potentialRatio β t (U e)‖ * density t
  let f (t : ℝ) := Real.log |1 - x ^ 2 / t ^ 2| * density t
  let K := ((‖S‖ + 1) ^ 2 + β ^ 2) * D
  let μ := volume.restrict (Ioi β)
  have hS : 0 ≤ S.re := (realSaddleRoot_spec hβ hx).1
  have hU (e : ℝ) (he : 0 < e) : 0 < (U e).re := by
    simpa only [U, Complex.add_re, Complex.ofReal_re] using add_pos_of_nonneg_of_pos hS he
  have hhol (e : ℝ) (he : 0 < e) :=
    (holomorphicPotential_integrable_and_differentiable hβ bins.continuous_density hd (U e) (hU e he)).1
  have heq (e : ℝ) (he : 0 < e) : (holomorphicPotential β density (U e)).re = ∫ t, F e t ∂μ := by
    unfold holomorphicPotential
    have h := Complex.reCLM.integral_comp_comm (hhol e he)
    change (∫ t, (Complex.log (potentialRatio β t (U e)) * (density t : ℂ)).re ∂μ) =
      (∫ t, Complex.log (potentialRatio β t (U e)) * (density t : ℂ) ∂μ).re at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with t
    simp [F, Complex.mul_re, Complex.log_re]
  have hfi : Integrable f μ := bins.realPotential_integrable hβ (fun t ht => (hd t ht).2) hx
  have hae : ∀ᵐ t ∂μ, β < t ∧ t ≠ x := by
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ x := by rw [ae_iff]; simp
    exact (ae_restrict_mem measurableSet_Ioi).and (ae_restrict_of_ae hne)
  have hbase (t : ℝ) (ht : β < t) (htx : t ≠ x) : 0 < |1 - x ^ 2 / t ^ 2| := by
    apply abs_pos.mpr
    intro he
    have ht' := hβ.trans ht
    have hpow : x ^ 2 = t ^ 2 := by
      have he' : x ^ 2 / t ^ 2 = 1 := by linarith
      exact (div_eq_iff (sq_pos_of_pos ht').ne').mp he' |>.trans (one_mul _)
    exact htx ((sq_eq_sq₀ ht'.le hx).mp hpow.symm)
  have hFbound (e : ℝ) (he : 0 < e) (he1 : e < 1)
      (t : ℝ) (ht : β < t) (htx : t ≠ x) :
      ‖F e t‖ ≤ ‖f t‖ + K * (t ^ 2)⁻¹ := by
    have hd' := hd t ht.le
    have ht0 := hβ.trans ht
    have hlow : |1 - x ^ 2 / t ^ 2| ≤ ‖potentialRatio β t (U e)‖ := by
      have h := potentialRatio_norm_mono_real hβ ht.le hS he.le
      rw [show potentialRatio β t S = _ from potentialRatio_boundary hβ hx,
        Complex.norm_real, Real.norm_eq_abs] at h
      exact h
    have hpos := (hbase t ht htx).trans_le hlow
    have hloglow : f t ≤ F e t := mul_le_mul_of_nonneg_right
      (Real.log_le_log (hbase t ht htx) hlow) hd'.1
    have hnormU : ‖U e‖ ≤ ‖S‖ + 1 := by
      calc
        _ ≤ ‖S‖ + ‖(e : ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by rw [Complex.norm_of_nonneg he.le]; linarith
    let C := (‖S‖ + 1) ^ 2 + β ^ 2
    have hnorm : ‖potentialRatio β t (U e)‖ ≤ 1 + C / t ^ 2 := by
      calc
        _ ≤ 1 + ‖(U e ^ 2 - (β : ℂ) ^ 2) / (t : ℂ) ^ 2‖ := by
          simpa only [potentialRatio, norm_one] using norm_add_le (1 : ℂ) ((U e ^ 2 - (β : ℂ) ^ 2) / (t : ℂ) ^ 2)
        _ ≤ _ := by
          rw [norm_div, norm_pow (t : ℂ), Complex.norm_of_nonneg ht0.le]
          apply add_le_add_right (div_le_div_of_nonneg_right _ (by positivity : 0 ≤ t ^ 2))
          calc
            _ ≤ ‖U e ^ 2‖ + ‖(β : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ C := by
              simp only [C, norm_pow, Complex.norm_of_nonneg hβ.le]
              exact add_le_add_left (pow_le_pow_left₀ (norm_nonneg _) hnormU 2) _
    have hloghi : F e t ≤ K * (t ^ 2)⁻¹ := by
      have h := (Real.log_le_sub_one_of_pos hpos).trans (sub_le_sub_right hnorm 1)
      have h' : Real.log ‖potentialRatio β t (U e)‖ ≤ C / t ^ 2 := by linarith
      calc
        _ ≤ (C / t ^ 2) * D :=
          mul_le_mul h' hd'.2 hd'.1 (by dsimp [C]; positivity)
        _ = _ := by dsimp [K, C]; ring
    have hk : 0 ≤ K * (t ^ 2)⁻¹ := by
      have hD := hd'.1.trans hd'.2
      dsimp [K]
      positivity
    rw [Real.norm_eq_abs, abs_le, Real.norm_eq_abs]
    constructor
    · linarith [neg_abs_le (f t)]
    · linarith [abs_nonneg (f t)]
  have hright0 : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e := self_mem_nhdsWithin
  have hright1 : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
  have hright := hright0.and hright1
  have hlim : Tendsto (fun e : ℝ => ∫ t, F e t ∂μ) (𝓝[>] 0) (𝓝 (∫ t, f t ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖ + K * (t ^ 2)⁻¹)
    · refine hright.mono fun e he => ?_
      exact (Complex.continuous_re.comp_aestronglyMeasurable
        (hhol e he.1).aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun t => by simp [F, Complex.mul_re, Complex.log_re])
    · exact hright.mono fun e he => hae.mono fun t ht => hFbound e he.1 he.2 t ht.1 ht.2
    · exact hfi.norm.add ((integrableOn_inv_sq hβ).const_mul K)
    · filter_upwards [hae] with t ht
      have h0 : potentialRatio β t (U 0) = ((1 - x ^ 2 / t ^ 2 : ℝ) : ℂ) := by
        simpa [U, S] using (potentialRatio_boundary (t := t) hβ hx)
      have hc : Continuous (fun e : ℝ => ‖potentialRatio β t (U e)‖) := by
        unfold potentialRatio U
        fun_prop
      have hn : ‖potentialRatio β t (U 0)‖ ≠ 0 := by
        rw [h0, Complex.norm_real, Real.norm_eq_abs]
        exact (hbase t ht.1 ht.2).ne'
      have harg : Tendsto (fun e : ℝ => ‖potentialRatio β t (U e)‖)
          (𝓝 0) (𝓝 ‖potentialRatio β t (U 0)‖) := hc.continuousAt
      have hh : Tendsto (fun e : ℝ => F e t) (𝓝 0) (𝓝 (F 0 t)) :=
        ((Real.continuousAt_log hn).tendsto.comp harg).mul tendsto_const_nhds
      have hval : F 0 t = f t := by
        unfold F f
        rw [h0, Complex.norm_real, Real.norm_eq_abs]
      exact hval ▸ hh.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (hright.mono fun e he => (heq e he.1).symm)

private theorem saddle_realPotential_eval (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2) (x : ℝ) (hx : 0 ≤ x) :
    realPotential β (saddleDensity n β) x =
      (n : ℝ) * (a / 2 * ((realSaddleRoot β x).re - β) -
        spectralAverage (fun r => Real.log ‖realSaddleRoot β x + (radius β r : ℂ)‖) +
        saddleLogAverage β 0) := by
  obtain ⟨hc, hd, hp, hu⟩ := saddleDensity_spec n hn ha hβ hs
  let bins := EqualMassBins.ofDensity hc (fun t ht => (hd t ht).1) hp hu
  let S := realSaddleRoot β x
  let U (e : ℝ) := S + (max e 0 : ℝ)
  let J (e : ℝ) := spectralAverage (fun r => Real.log ‖U e + (radius β r : ℂ)‖)
  have hS : 0 ≤ S.re := (realSaddleRoot_spec hβ hx).1
  have hJ : Continuous J := by
    let f (e θ : ℝ) := Real.log ‖U e + (radius β (2 - 2 * Real.cos θ) : ℂ)‖
    have hfc : Continuous (Function.uncurry f) := by
      apply Continuous.log
      · unfold U radius
        fun_prop
      · rintro ⟨e, θ⟩
        apply norm_ne_zero_iff.mpr
        have hr : 0 < radius β (2 - 2 * Real.cos θ) := by unfold radius; positivity
        intro h
        have he := congrArg Complex.re h
        simp only [Function.uncurry, U, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at he
        linarith [le_max_right e 0]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc 0 Real.pi).div_const _
  let G (e : ℝ) := (n : ℝ) * (a / 2 * ((U e).re - β) - J e + saddleLogAverage β 0)
  have hcG : Continuous G := by
    unfold G
    have hU : Continuous U := by unfold U; fun_prop
    exact continuous_const.mul (((Complex.continuous_re.comp hU).sub continuous_const |>.const_mul (a / 2)).sub hJ |>.add continuous_const)
  have hlim := realPotential_boundary_limit hβ hx bins hd
  have hG := hcG.continuousAt (x := (0 : ℝ)) |>.continuousWithinAt (s := Ioi 0) |>.tendsto
  have heq : ∀ᶠ e : ℝ in 𝓝[>] 0, (holomorphicPotential β (saddleDensity n β) (S + (e : ℂ))).re = G e := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with e he
    have he0 : 0 < e := he
    have hUe : U e = S + (e : ℂ) := by dsimp [U]; rw [max_eq_left he0.le]
    have hre : 0 < (U e).re := by
      rw [hUe, Complex.add_re, Complex.ofReal_re]
      linarith
    have h := congrArg Complex.re
      (holomorphicPotential_eval n hn ha hβ hs (show 0 < (U e).re from hre))
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im, zero_div, zero_mul, sub_zero,
      Complex.sub_re, Complex.ofReal_re, complexSaddleLogAverage_re hβ hre.le] at h
    simpa only [G, J, hUe, Complex.ofReal_re] using h
  have h := tendsto_nhds_unique_of_eventuallyEq hlim hG heq
  simpa only [G, J, U, max_self, Complex.ofReal_zero, add_zero, S] using h

private theorem norm_axis_difference_sq (r x : ℝ) :
    ‖(r : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 = r ^ 2 + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, ← sq]

private theorem log_axis_comparison {R s r x : ℝ} (hR : 0 < R) (hs : 0 ≤ s)
    (hRs : s < R) (hsq : R ^ 2 - s ^ 2 = r ^ 2 + x ^ 2) :
    Real.log ‖(r : ℂ) - (x : ℂ) * Complex.I‖ + s / R ≤ Real.log (R + s) := by
  let d := ‖(r : ℂ) - (x : ℂ) * Complex.I‖
  have hd2 : d ^ 2 = (R + s) * (R - s) := by
    rw [show d ^ 2 = r ^ 2 + x ^ 2 from norm_axis_difference_sq r x, ← hsq]
    ring
  have hd : 0 < d := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro h
    change 0 = d at h
    rw [← h, zero_pow (by decide : 2 ≠ 0)] at hd2
    exact (mul_pos (add_pos_of_pos_of_nonneg hR hs) (sub_pos.mpr hRs)).ne' hd2.symm
  have hp : 0 < R + s := add_pos_of_pos_of_nonneg hR hs
  have hm : 0 < R - s := sub_pos.mpr hRs
  have hl := congrArg Real.log hd2
  rw [Real.log_pow, Real.log_mul hp.ne' hm.ne'] at hl
  norm_num at hl
  have hv : 0 ≤ 2 * s / (R - s) := by positivity
  have hb := Real.le_log_one_add_of_nonneg hv
  have he : 1 + 2 * s / (R - s) = (R + s) / (R - s) := by
    field_simp [hm.ne']
    ring
  have he' : 2 * (2 * s / (R - s)) / (2 * s / (R - s) + 2) = 2 * (s / R) := by
    field_simp [hm.ne', hR.ne', show 0 < 2 * s / (R - s) + 2 by linarith]
    <;> ring
  rw [he, he', Real.log_div hp.ne' hm.ne'] at hb
  change Real.log d + s / R ≤ _
  linarith

/-- The saddle multiplier cancels the exterior Joukowski radius on the real axis. -/
theorem saddle_real_cancellation (n : ℕ) (hn : 0 < (n : ℝ)) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hs : saddleMass β = a / 2) (ω : ℝ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ ζ + ζ⁻¹ = (ω : ℂ) * Complex.I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      realPotential β (saddleDensity n β) |ω| + (n : ℝ) * Real.log ‖ζ‖ ≤
        (n : ℝ) * saddleRate a β 0 := by
  obtain ⟨ζ, hz, hroot, houter⟩ := exists_outer_root ((ω : ℂ) * Complex.I - 2)
  obtain ⟨hgreen, hiG⟩ := angularGreen_eq_log_outer_radius ω hz hroot houter
  refine ⟨ζ, hz, hroot, houter, ?_⟩
  let x := |ω|
  let S := realSaddleRoot β x
  let Gamma := spectralAverage (fun r => Real.log ‖(r : ℂ) - (ω : ℂ) * Complex.I‖)
  let J := spectralAverage (fun r => Real.log ‖S + (radius β r : ℂ)‖)
  have hx : 0 ≤ x := abs_nonneg ω
  have hx2 : x ^ 2 = ω ^ 2 := sq_abs ω
  have hβ0 : radius β 0 = β := by simp [radius, Real.sqrt_sq hβ.le]
  suffices hh : a / 2 * S.re + Gamma ≤ J by
    rw [saddle_realPotential_eval n hn ha hβ hs x hx, ← hgreen]
    change (n : ℝ) * (a / 2 * (S.re - β) - J + saddleLogAverage β 0) + (n : ℝ) * Gamma ≤ _
    have he : saddleRate a β 0 = saddleLogAverage β 0 - a / 2 * β := by
      simp [saddleRate, saddleLogAverage, hβ0]
    rw [he]
    have h := mul_le_mul_of_nonneg_left hh (show 0 ≤ (n : ℝ) by positivity)
    linarith
  by_cases hsx : x ≤ β
  · let s := Real.sqrt (β ^ 2 - x ^ 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = β ^ 2 - x ^ 2 := by
      exact Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hx hsx 2))
    have hS : S = (s : ℂ) := by simp [S, s, realSaddleRoot, hsx]
    have hJ : J = spectralAverage (fun r => Real.log (radius β r + s)) := by
      unfold J
      simp_rw [hS, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
      apply congrArg (fun f => spectralAverage f)
      funext r
      rw [abs_of_nonneg (add_nonneg hs0
        (show 0 ≤ radius β r from Real.sqrt_nonneg _)), add_comm]
    rw [hS, Complex.ofReal_re, hJ]
    let p (θ : ℝ) := 2 - 2 * Real.cos θ
    let g (θ : ℝ) := Real.log ‖(p θ : ℂ) - (ω : ℂ) * Complex.I‖
    let G (θ : ℝ) := (radius β (p θ))⁻¹
    let H (θ : ℝ) := Real.log (radius β (p θ) + s)
    have hP (θ : ℝ) : 0 < radius β (p θ) := by unfold radius; positivity
    have hcG : Continuous G := by
      apply Continuous.inv₀ (by dsimp [radius, p]; fun_prop)
      exact fun θ => (hP θ).ne'
    have hcH : Continuous H := by
      apply Continuous.log (by dsimp [radius, p]; fun_prop)
      exact fun θ => (add_pos_of_pos_of_nonneg (hP θ) hs0).ne'
    have hb (θ : ℝ) (ht : θ ∈ Ioo 0 Real.pi) : s * G θ + g θ ≤ H θ := by
      have hcos := Real.strictAntiOn_cos
        (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
        ⟨ht.1.le, ht.2.le⟩ ht.1
      have hp : 0 < p θ := by dsimp [p]; rw [Real.cos_zero] at hcos; linarith
      have hR2 : radius β (p θ) ^ 2 = (p θ) ^ 2 + β ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hRs : s < radius β (p θ) :=
        (sq_lt_sq₀ hs0 (hP θ).le).1 (by rw [hR2, hs2]; nlinarith [sq_pos_of_pos hp])
      have h := log_axis_comparison (hP θ) hs0 hRs (show
        radius β (p θ) ^ 2 - s ^ 2 = (p θ) ^ 2 + ω ^ 2 by rw [hR2, hs2, hx2]; ring)
      simpa only [H, g, G, div_eq_mul_inv, add_comm] using h
    have hiG' : IntervalIntegrable g volume 0 Real.pi := hiG
    have h := intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le
      (((hcG.intervalIntegrable (μ := volume) 0 Real.pi).const_mul s).add hiG')
      (hcH.intervalIntegrable _ _) hb
    rw [intervalIntegral.integral_add
      ((hcG.intervalIntegrable (μ := volume) 0 Real.pi).const_mul s) hiG',
      intervalIntegral.integral_const_mul] at h
    have hm : (∫ θ in 0..Real.pi, G θ) / Real.pi = a / 2 := hs
    have hmul := div_le_div_of_nonneg_right h Real.pi_pos.le
    rw [add_div, mul_div_assoc, hm, mul_comm s (a / 2)] at hmul
    exact hmul
  · have hxβ : β < x := lt_of_not_ge hsx
    let c := Real.sqrt (x ^ 2 - β ^ 2)
    have hc : c ^ 2 = x ^ 2 - β ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ hβ.le hxβ.le 2))
    have hS : S = (c : ℂ) * Complex.I := by simp [S, c, realSaddleRoot, hsx]
    have hre : S.re = 0 := by rw [hS]; simp [Complex.mul_re]
    have hnrm (r : ℝ) : ‖S + (radius β r : ℂ)‖ = ‖(r : ℂ) - (ω : ℂ) * Complex.I‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
      rw [norm_axis_difference_sq, hS, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, add_zero, sub_zero, zero_add, zero_pow (by decide : 2 ≠ 0), ← sq]
      rw [hc, show radius β r ^ 2 = r ^ 2 + β ^ 2 from Real.sq_sqrt (by positivity), hx2]
      ring
    rw [hre, mul_zero, zero_add]
    simp only [J, Gamma, hnrm, le_refl]

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
