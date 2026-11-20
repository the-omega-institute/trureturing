/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RHPowerThreshold
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RHPowerThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH, division by a real power sends the integrated Mangoldt remainder to zero precisely above the square-root exponent. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RHPowerThreshold

private lemma normalized_at_exp (θ y : ℝ) :
    U (Real.exp y) / (Real.exp y) ^ θ =
      G y * Real.exp (y * (1 / 2 - θ)) := by
  rw [G, ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
  calc
    U (Real.exp y) * Real.exp (-(y * θ)) =
        U (Real.exp y) * (Real.exp (-y / 2) * Real.exp (y * (1 / 2 - θ))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

/-- For the complete inclusive Mangoldt remainder, the power-normalized
primitive tends to zero exactly above the critical exponent, under RH. -/
theorem u_div_rpow_tendsto_zero_iff (hRH : RiemannHypothesis) (θ : ℝ) :
    Tendsto (fun x : ℝ => U x / x ^ θ) atTop (𝓝 0) ↔ 1 / 2 < θ := by
  obtain ⟨hbound, hrecur⟩ := actual_G_control hRH
  constructor
  · intro hzero
    by_contra! hθ
    have hmass : 0 < firstLiMass := by
      unfold firstLiMass
      linarith [first_li_coefficient_pos]
    have hhalf : 0 < firstLiMass / 2 := half_pos hmass
    have hsmall := (hzero.comp Real.tendsto_exp_atTop).eventually_lt_const hhalf
    obtain ⟨Y, hY⟩ := eventually_atTop.1 hsmall
    obtain ⟨n, hn, hpeak⟩ := hrecur _ hhalf Y
    have hG : firstLiMass / 2 < G n := by
      linarith [(abs_lt.mp hpeak).1]
    have hfactor : 1 ≤ Real.exp ((n : ℝ) * (1 / 2 - θ)) :=
      Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hθ))
    have hlow : G n ≤ G n * Real.exp ((n : ℝ) * (1 / 2 - θ)) :=
      le_mul_of_one_le_right (hhalf.le.trans hG.le) hfactor
    have hupper : U (Real.exp n) / (Real.exp n) ^ θ < firstLiMass / 2 := hY n hn
    rw [normalized_at_exp] at hupper
    exact (hG.trans_le hlow).not_ge hupper.le
  · intro hθ
    have hdecay : Tendsto (fun y : ℝ => Real.exp (y * (1 / 2 - θ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.mpr hθ))
    have hlogScale : Tendsto (fun y : ℝ => U (Real.exp y) / (Real.exp y) ^ θ)
        atTop (𝓝 0) := by
      apply squeeze_zero_norm' (a := fun y : ℝ =>
        (firstLiMass + 1) * Real.exp (y * (1 / 2 - θ))) ?_
        (by simpa using hdecay.const_mul (firstLiMass + 1))
      filter_upwards [hbound 1 zero_lt_one] with y hy
      rw [normalized_at_exp, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hy.le (Real.exp_nonneg _)
    apply (hlogScale.comp Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Function.comp_def, Real.exp_log hx]

end D5.S3.Weil.Mertens.IntegratedExplicit.RHPowerThreshold
