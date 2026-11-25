/- GID: D5/S3/Weil/Mertens/WeightedTailBudgetReduction
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/WeightedTailBudgetReduction
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Two-sided finite weighted tail budget comparison from a one-sided power bound. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Mertens.WeightedTailWindowMass

/-! A finite comparison for the logarithmically weighted negative budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.WeightedTailBudgetReduction

open Real Set MeasureTheory
open WeightedTailTransport (tail weightedTail r density transport)
open WeightedTailInverse (a a_pos)
open WeightedTailWindowMass (weightedNegativeMass endpointDefect)

open private density_nonneg density_integrable density_mass from
  D5.S3.Weil.Mertens.WeightedTailTransport
open private r_mul_a from D5.S3.Weil.Mertens.WeightedTailInverse
open private a_continuousOn weightedTail_continuousOn from
  D5.S3.Weil.Mertens.WeightedTailWindowMass

noncomputable section

/-- The signed density tail in logarithmic transport. -/
private def densityTail (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Ioi t, density u * tail k u

/-- The positive local tail with the signed density tail at the cutoff. -/
def reducedDensityTail (k : ℝ → ℝ) (C t : ℝ) : ℝ :=
  densityTail k C + ∫ u in t..C, density u * max (tail k u) 0

/-- The negative local density tail omitted by the reduction. -/
private def negativeDensityWindow (k : ℝ → ℝ) (C t : ℝ) : ℝ :=
  ∫ u in t..C, density u * max (-tail k u) 0

private lemma density_mul_max_integrable {f : ℝ → ℝ} {Y : ℝ} (hY : 1 < Y)
    (hf : IntegrableOn (fun u => density u * f u) (Ioi Y)) :
    IntegrableOn (fun u => density u * max (f u) 0) (Ioi Y) := by
  refine (hf.sup (integrable_zero ℝ ℝ _)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change max (density u * f u) 0 = density u * max (f u) 0
  rw [mul_max_of_nonneg _ _ (density_nonneg (hY.trans hu)), mul_zero]

/-- Splitting the signed density tail at `C` leaves an omitted nonnegative
term whose normalized size is controlled by the one-sided bound on `[Y, C]`. -/
private theorem finite_split {k : ℝ → ℝ} {Y C t κ : ℝ}
    (hY : 2 ≤ Y) (ht : t ∈ Icc Y C) (hκ : κ ≤ 1 / 2)
    (hk : IntegrableOn k (Ioi Y))
    (hneg : ∀ u ∈ Icc Y C, max (-tail k u) 0 ≤ u ^ (κ - 1 / 2)) :
    densityTail k t = reducedDensityTail k C t - negativeDensityWindow k C t ∧
      0 ≤ a t * negativeDensityWindow k C t ∧
      a t * negativeDensityWindow k C t ≤ t ^ (κ - 1 / 2) := by
  have ht2 := hY.trans ht.1
  have ht1 : 1 < t := by linarith
  have ha := (a_pos ht1).le
  have hkt := hk.mono_set (Ioi_subset_Ioi ht.1)
  have hdQ := (transport ht2 hkt).2.1
  have hp := density_mul_max_integrable ht1 hdQ
  have hn := density_mul_max_integrable (f := fun u => -tail k u) ht1
    (by simpa only [mul_neg, Pi.neg_def] using hdQ.neg)
  have hpI := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).2
    (hp.mono_set Ioc_subset_Ioi_self)
  have hnI := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).2
    (hn.mono_set Ioc_subset_Ioi_self)
  have hsplit : densityTail k t - densityTail k C =
      (∫ u in t..C, density u * max (tail k u) 0) - negativeDensityWindow k C t := by
    rw [densityTail, densityTail, intervalIntegral.integral_Ioi_sub_Ioi hdQ ht.2,
      negativeDensityWindow, ← intervalIntegral.integral_sub hpI hnI]
    simp only [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  have hd := density_integrable ht2
  have hdI := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).2
    (hd.mono_set Ioc_subset_Ioi_self)
  have hmass : (∫ u in t..C, density u) ≤ r t := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi hd ht.2, density_mass ht2]
    exact sub_le_self _ (setIntegral_nonneg measurableSet_Ioi
      (fun u hu => density_nonneg (ht1.trans (ht.2.trans_lt hu))))
  have hpow : 0 ≤ t ^ (κ - 1 / 2) := rpow_nonneg (by linarith) _
  have hnBound : negativeDensityWindow k C t ≤ (∫ u in t..C, density u) * t ^ (κ - 1 / 2) := by
    rw [negativeDensityWindow, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on ht.2 hnI (hdI.mul_const _) ?_
    intro u hu
    exact mul_le_mul_of_nonneg_left
      ((hneg u ⟨ht.1.trans hu.1, hu.2⟩).trans
        (rpow_le_rpow_of_nonpos (by linarith) hu.1 (sub_nonpos.mpr hκ)))
      (density_nonneg (ht1.trans_le hu.1))
  refine ⟨by unfold reducedDensityTail; linarith only [hsplit], ?_, ?_⟩
  · exact mul_nonneg ha (intervalIntegral.integral_nonneg ht.2 (fun u hu =>
      mul_nonneg (density_nonneg (ht1.trans_le hu.1)) (le_max_right _ _)))
  · calc
      _ ≤ a t * (r t * t ^ (κ - 1 / 2)) :=
        mul_le_mul_of_nonneg_left (hnBound.trans (mul_le_mul_of_nonneg_right hmass hpow)) ha
      _ = _ := by rw [← mul_assoc, mul_comm (a t) (r t), r_mul_a ht1, one_mul]

private lemma endpointDefect_eq_densityTail {k : ℝ → ℝ} {t : ℝ} (ht : 2 ≤ t)
    (hk : IntegrableOn k (Ioi t)) : endpointDefect k t = a t * densityTail k t := by
  have ht1 : 1 < t := by linarith
  calc
    endpointDefect k t = a t * (tail k t * r t - weightedTail k t) := by
      unfold endpointDefect
      rw [mul_sub, mul_left_comm, mul_comm (a t) (r t), r_mul_a ht1, mul_one]
    _ = _ := congrArg (a t * ·) (transport ht hk).2.2

/-- Before taking positive parts, the normalized difference is the difference
of two nonnegative quantities bounded by the same power. -/
private theorem normalized_window_error {k : ℝ → ℝ} {Y C t κ : ℝ}
    (hY : 2 ≤ Y) (ht : t ∈ Icc Y C) (hκ : κ ≤ 1 / 2)
    (hk : IntegrableOn k (Ioi Y))
    (hneg : ∀ u ∈ Icc Y C, max (-tail k u) 0 ≤ u ^ (κ - 1 / 2)) :
    let δ := a t * (-weightedTail k t) - (a t * reducedDensityTail k C t - max (tail k t) 0)
    δ = max (-tail k t) 0 - a t * negativeDensityWindow k C t ∧ |δ| ≤ t ^ (κ - 1 / 2) := by
  obtain ⟨hsplit, hn0, hn⟩ := finite_split hY ht hκ hk hneg
  have hnorm := endpointDefect_eq_densityTail (hY.trans ht.1) (hk.mono_set (Ioi_subset_Ioi ht.1))
  rw [endpointDefect, hsplit, mul_sub] at hnorm
  have hdiff : a t * (-weightedTail k t) - (a t * reducedDensityTail k C t - max (tail k t) 0) =
      max (-tail k t) 0 - a t * negativeDensityWindow k C t := by
    rw [mul_neg]
    linarith only [hnorm, max_zero_sub_max_neg_zero_eq_self (tail k t)]
  refine ⟨hdiff, ?_⟩
  rw [hdiff]
  exact abs_le.2 ⟨by linarith only [hn, le_max_right (-tail k t) 0],
    by linarith only [hneg t ht, hn0]⟩

/-- The negative endpoint payment increases by at most the normalized omitted
density mass at `B`. -/
private lemma endpoint_error {k : ℝ → ℝ} {Y B C κ : ℝ}
    (hY : 2 ≤ Y) (hB : B ∈ Icc Y C) (hκ : κ ≤ 1 / 2)
    (hk : IntegrableOn k (Ioi Y))
    (hneg : ∀ u ∈ Icc Y C, max (-tail k u) 0 ≤ u ^ (κ - 1 / 2)) :
    let E := max (-endpointDefect k B) 0 - max (-(a B * reducedDensityTail k C B)) 0
    0 ≤ E ∧ E ≤ a B * negativeDensityWindow k C B ∧
      a B * negativeDensityWindow k C B ≤ B ^ (κ - 1 / 2) := by
  obtain ⟨hsplit, hn0, hn⟩ := finite_split hY hB hκ hk hneg
  have hdefect : -endpointDefect k B =
      -(a B * reducedDensityTail k C B) + a B * negativeDensityWindow k C B := by
    rw [endpointDefect_eq_densityTail (hY.trans hB.1) (hk.mono_set (Ioi_subset_Ioi hB.1)),
      hsplit, mul_sub, neg_sub, add_comm, sub_eq_add_neg]
  dsimp only
  rw [hdefect]
  refine ⟨?_, ?_, hn⟩
  · exact sub_nonneg.2 (max_le_max (le_add_of_nonneg_right hn0) le_rfl)
  · refine (max_sub_max_le_max _ _ _ _).trans ?_
    rw [add_sub_cancel_left, sub_self, max_eq_left hn0]

/-- The finite weighted negative budget is within one integrated power error
of the reduced window, with an additional one-sided endpoint error. -/
theorem budget_bounds {k : ℝ → ℝ} {Y B C κ : ℝ}
    (hY : 2 ≤ Y) (hYB : Y ≤ B) (hBC : B ≤ C) (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hk : IntegrableOn k (Ioi Y))
    (hneg : ∀ t ∈ Icc Y C, max (-tail k t) 0 ≤ t ^ (κ - 1 / 2)) :
    let W := weightedNegativeMass k Y B +
      sqrt Y * max (-(tail k B - a B * weightedTail k B)) 0
    let Wred :=
      (∫ t in Y..B, max (a t * reducedDensityTail k C t - max (tail k t) 0) 0 / sqrt t) +
        sqrt Y * max (-(a B * reducedDensityTail k C B)) 0
    let M := (B ^ κ - Y ^ κ) / κ
    Wred - M ≤ W ∧ W ≤ Wred + M + sqrt Y * B ^ (κ - 1 / 2) := by
  have hY1 : 1 < Y := by linarith
  have hY0 := zero_lt_one.trans hY1
  have hYC := hYB.trans hBC
  have ha := a_continuousOn (B := B) hY1
  have hQ : ContinuousOn (tail k) (Icc Y B) :=
    hk.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)
  have hp := density_mul_max_integrable hY1 (transport hY hk).2.1
  have hpC : IntegrableOn (fun u => density u * max (tail k u) 0) (uIcc Y C) := by
    rw [uIcc_of_le hYC, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hp.mono_set Ioc_subset_Ioi_self
  have hF : ContinuousOn (reducedDensityTail k C) (Icc Y B) :=
    continuousOn_const.add ((intervalIntegral.continuousOn_primitive_interval_left hpC).mono
      (uIcc_of_le hYC ▸ Icc_subset_Icc le_rfl hBC))
  let f (t : ℝ) := max (a t * (-weightedTail k t)) 0 / sqrt t
  let g (t : ℝ) := max (a t * reducedDensityTail k C t - max (tail k t) 0) 0 / sqrt t
  have hsqrt (t : ℝ) (ht : t ∈ Icc Y B) : sqrt t ≠ 0 := (sqrt_pos.2 (hY0.trans_le ht.1)).ne'
  have hf : ContinuousOn f (Icc Y B) :=
    ((ha.mul (weightedTail_continuousOn hY hk).neg).sup continuousOn_const).div
      continuous_sqrt.continuousOn hsqrt
  have hg : ContinuousOn g (Icc Y B) :=
    (((ha.mul hF).sub (hQ.sup continuousOn_const)).sup continuousOn_const).div
      continuous_sqrt.continuousOn hsqrt
  have hmass : weightedNegativeMass k Y B = ∫ t in Y..B, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hYB] at ht
    change (a t / sqrt t) * max (-weightedTail k t) 0 = f t
    dsimp [f]
    rw [← mul_div_right_comm, mul_max_of_nonneg _ _ (a_pos (hY1.trans_le ht.1)).le, mul_zero]
  have hpoint (t : ℝ) (ht : t ∈ Icc Y B) : |f t - g t| ≤ t ^ (κ - 1) := by
    have ht0 := hY0.trans_le ht.1
    have herr := (normalized_window_error hY ⟨ht.1, ht.2.trans hBC⟩ hκhalf hk hneg).2
    dsimp [f, g]
    rw [← sub_div, abs_div, abs_of_nonneg (sqrt_nonneg t)]
    calc
      _ ≤ t ^ (κ - 1 / 2) / sqrt t :=
        div_le_div_of_nonneg_right ((abs_max_sub_max_le_abs _ _ _).trans herr) (sqrt_nonneg t)
      _ = _ := by rw [sqrt_eq_rpow, ← rpow_sub ht0, show κ - 1 / 2 - 1 / 2 = κ - 1 by ring]
  have hpowI : IntervalIntegrable (fun t : ℝ => t ^ (κ - 1)) volume Y B :=
    ContinuousOn.intervalIntegrable_of_Icc hYB
      (continuousOn_id.rpow_const (fun _ ht => Or.inl (hY0.trans_le ht.1).ne'))
  have hpower : (∫ t in Y..B, t ^ (κ - 1)) = (B ^ κ - Y ^ κ) / κ := by
    rw [integral_rpow (Or.inl (by linarith : -1 < κ - 1)), sub_add_cancel]
  have hwindow : |weightedNegativeMass k Y B - ∫ t in Y..B, g t| ≤ (B ^ κ - Y ^ κ) / κ := by
    rw [hmass, ← intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc hYB)
      (hg.intervalIntegrable_of_Icc hYB), ← hpower]
    exact (intervalIntegral.abs_integral_le_integral_abs hYB).trans
      (intervalIntegral.integral_mono_on hYB ((hf.sub hg).abs.intervalIntegrable_of_Icc hYB)
        hpowI hpoint)
  obtain ⟨he0, he, hePow⟩ := endpoint_error hY ⟨hYB, hBC⟩ hκhalf hk hneg
  have hE0 := mul_nonneg (sqrt_nonneg Y) he0
  have hE := mul_le_mul_of_nonneg_left (he.trans hePow) (sqrt_nonneg Y)
  obtain ⟨hlo, hhi⟩ := abs_le.1 hwindow
  change _ ≤ _ ∧ _ ≤ _
  change _ ≤ weightedNegativeMass k Y B + sqrt Y * max (-endpointDefect k B) 0 ∧
    weightedNegativeMass k Y B + sqrt Y * max (-endpointDefect k B) 0 ≤ _
  constructor <;> linarith only [hlo, hhi, hE0, hE]

#print axioms budget_bounds

end
end D5.S3.Weil.Mertens.WeightedTailBudgetReduction
