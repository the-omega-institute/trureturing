/- GID: D5/S3/Analytic/KummerRatio/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Order.IntermediateValue, mathlib/module/Mathlib.Topology.Order.DenselyOrdered, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Strict monotonicity and exact Gamma quotient ranges of the upper parameter Kummer ratio. -/

import D5.S3.Analytic.KummerRatio.Transform
import D5.S3.Analytic.KummerRatio.Comparison
import D5.S3.Analytic.KummerRatio.Asymptotics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Set Filter Topology
open D5.S3.Analytic.KummerRatio.Defs D5.S3.Analytic.KummerRatio.Series
open D5.S3.Analytic.KummerRatio.Transform
open D5.S3.Analytic.KummerRatio.Asymptotics

namespace D5.S3.Analytic.KummerRatio.Result

private lemma ratio_transform (a b c δ x : ℝ) (hc : 0 < c) :
    ratio a b c δ x = ratio (c-b-δ) (c-a-δ) c δ (-x) := by
  unfold ratio
  rw [kummer_transform (b+δ) hc x, kummer_transform a hc x,
    kummer_transform (a+δ) hc x, kummer_transform b hc x]
  rw [show c - b - δ + δ = c-b by ring,
    show c - a - δ + δ = c-a by ring,
    show c - (b+δ) = c-b-δ by ring,
    show c - (a+δ) = c-a-δ by ring]
  have hnum : (Real.exp x * kummer (c-b-δ) c (-x)) *
      (Real.exp x * kummer (c-a) c (-x)) =
      (Real.exp x)^2 * (kummer (c-a) c (-x) * kummer (c-b-δ) c (-x)) := by ring
  have hden : (Real.exp x * kummer (c-a-δ) c (-x)) *
      (Real.exp x * kummer (c-b) c (-x)) =
      (Real.exp x)^2 * (kummer (c-b) c (-x) * kummer (c-a-δ) c (-x)) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 (Real.exp_ne_zero x))]

private lemma normalized_ratio (a b c δ x : ℝ) (hx : 0 < x) :
    (Real.exp (-x) * x^(c-(b+δ)) * kummer (b+δ) c x) *
      (Real.exp (-x) * x^(c-a) * kummer a c x) /
    ((Real.exp (-x) * x^(c-(a+δ)) * kummer (a+δ) c x) *
      (Real.exp (-x) * x^(c-b) * kummer b c x)) = ratio a b c δ x := by
  let C : ℝ := (Real.exp (-x))^2 * x^(2*c-a-b-δ)
  have hnum :
      (Real.exp (-x) * x^(c-(b+δ)) * kummer (b+δ) c x) *
        (Real.exp (-x) * x^(c-a) * kummer a c x) =
      C * (kummer (b+δ) c x * kummer a c x) := by
    calc
      _ = (Real.exp (-x))^2 * (x^(c-(b+δ)) * x^(c-a)) *
          (kummer (b+δ) c x * kummer a c x) := by ring
      _ = _ := by
        rw [← Real.rpow_add hx, show c-(b+δ)+(c-a) = 2*c-a-b-δ by ring]
  have hden :
      (Real.exp (-x) * x^(c-(a+δ)) * kummer (a+δ) c x) *
        (Real.exp (-x) * x^(c-b) * kummer b c x) =
      C * (kummer (a+δ) c x * kummer b c x) := by
    calc
      _ = (Real.exp (-x))^2 * (x^(c-(a+δ)) * x^(c-b)) *
          (kummer (a+δ) c x * kummer b c x) := by ring
      _ = _ := by
        rw [← Real.rpow_add hx, show c-(a+δ)+(c-b) = 2*c-a-b-δ by ring]
  have hC : C ≠ 0 := (mul_pos (sq_pos_of_pos (Real.exp_pos _))
    (Real.rpow_pos_of_pos hx _)).ne'
  rw [hnum, hden, mul_div_mul_left _ _ hC]
  rfl

private lemma image_positive_ray {f : ℝ → ℝ} {L U : ℝ}
    (hf : ContinuousOn f (Ioi 0)) (hm : StrictAntiOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] 0) (𝓝 U)) (hinf : Tendsto f atTop (𝓝 L)) :
    f '' Ioi 0 = Ioo L U := by
  have hlo (t : ℝ) (ht : 0 < t) : L ≤ f t := by
    apply le_of_tendsto hinf
    filter_upwards [eventually_gt_atTop t] with x hx
    exact (hm ht (ht.trans hx) hx).le
  have hhi (t : ℝ) (ht : 0 < t) : f t ≤ U := by
    apply ge_of_tendsto hzero
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds] with x hx hxt
    exact (hm hx ht hxt).le
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change 0 < x at hx
    constructor
    · exact (hlo (x+1) (by linarith)).trans_lt (hm hx (show x+1 ∈ Ioi (0 : ℝ) from by change 0 < x+1; linarith) (by linarith))
    · exact (hm (by linarith : 0 < x/2) hx (by linarith)).trans_le (hhi (x/2) (by linarith))
  · exact isPreconnected_Ioi.intermediate_value_Ioo
      (l₁ := (atTop : Filter ℝ)) (l₂ := 𝓝[>] (0 : ℝ))
      (le_principal_iff.mpr (eventually_gt_atTop (0 : ℝ))) inf_le_right hf hinf hzero

private lemma ratio_tendsto_atTop
    {a b c δ : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hδ : 0 < δ) :
    Tendsto (ratio a b c δ) atTop
      (𝓝 (Real.Gamma (a+δ) * Real.Gamma b /
        (Real.Gamma (b+δ) * Real.Gamma a))) := by
  have hb : 0 < b := ha.trans hab
  have haδ : 0 < a+δ := add_pos ha hδ
  have hbδ : 0 < b+δ := add_pos hb hδ
  have hcΓ := (Real.Gamma_pos_of_pos hc).ne'
  have haΓ := (Real.Gamma_pos_of_pos ha).ne'
  have hbΓ := (Real.Gamma_pos_of_pos hb).ne'
  have haδΓ := (Real.Gamma_pos_of_pos haδ).ne'
  have hbδΓ := (Real.Gamma_pos_of_pos hbδ).ne'
  have h := ((tendsto_kummer_atTop hbδ hc).mul (tendsto_kummer_atTop ha hc)).div
    ((tendsto_kummer_atTop haδ hc).mul (tendsto_kummer_atTop hb hc))
    (mul_ne_zero (div_ne_zero hcΓ haδΓ) (div_ne_zero hcΓ hbΓ))
  have he : (Real.Gamma c / Real.Gamma (b+δ)) * (Real.Gamma c / Real.Gamma a) /
      ((Real.Gamma c / Real.Gamma (a+δ)) * (Real.Gamma c / Real.Gamma b)) =
      Real.Gamma (a+δ) * Real.Gamma b / (Real.Gamma (b+δ) * Real.Gamma a) := by
    field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact normalized_ratio a b c δ x hx

private lemma continuous_ratio_pos {a b c δ : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hδ : 0 < δ) :
    ContinuousOn (ratio a b c δ) (Ici 0) := by
  have hp (s : ℝ) (hs : 0 ≤ s) (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) :
      kummer s c x ≠ 0 := by
    have h := one_le_kummer hs hc hx
    linarith
  exact ((continuous_kummer (b+δ) hc).continuousOn.mul
    (continuous_kummer a hc).continuousOn).div
    ((continuous_kummer (a+δ) hc).continuousOn.mul
      (continuous_kummer b hc).continuousOn)
    (fun x hx => mul_ne_zero (hp (a+δ) (by linarith) x hx) (hp b (by linarith) x hx))

private lemma ratio_image_positive
    {a b c δ : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hδ : 0 < δ)
    (hm : StrictAntiOn (ratio a b c δ) (Ioi 0)) :
    ratio a b c δ '' Ioi 0 =
      Ioo (Real.Gamma (a+δ) * Real.Gamma b / (Real.Gamma (b+δ) * Real.Gamma a)) 1 := by
  have hf := continuous_ratio_pos ha hab hc hδ
  have hz : Tendsto (ratio a b c δ) (𝓝[>] 0) (𝓝 1) := by
    have h := (hf 0 (by simp)).mono (show Ioi (0 : ℝ) ⊆ Ici 0 from Ioi_subset_Ici_self)
    simpa [ratio, kummer_zero] using h.tendsto
  exact image_positive_ray (hf.mono Ioi_subset_Ici_self) hm hz
    (ratio_tendsto_atTop ha hab hc hδ)

/-- Both strict monotonicity statements and the exact open interval images of the
shifted upper parameter Kummer ratio. -/
theorem result : claim := by
  let decreasing := @_root_.D5.S3.Analytic.KummerRatio.Comparison.ratio_strictAntiOn
  intro a b c δ hc hδ
  constructor
  · intro ha hab
    exact ⟨decreasing ha hab hc hδ,
      ratio_image_positive ha hab hc hδ (decreasing ha hab hc hδ)⟩
  · intro hab hbc
    let u := c-b-δ
    let v := c-a-δ
    have hu : 0 < u := by dsimp [u]; linarith
    have huv : u < v := by dsimp [u, v]; linarith
    have hanti := decreasing hu huv hc hδ
    have hfun : ratio a b c δ = fun x => ratio u v c δ (-x) := by
      funext x
      exact ratio_transform a b c δ x hc
    constructor
    · intro x hx y hy hxy
      change x < 0 at hx
      change y < 0 at hy
      rw [hfun]
      exact hanti (show 0 < -y from neg_pos.mpr hy) (show 0 < -x from neg_pos.mpr hx) (neg_lt_neg hxy)
    · have him : (fun x => ratio u v c δ (-x)) '' Iio 0 = ratio u v c δ '' Ioi 0 := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨-x, (show 0 < -x from neg_pos.mpr hx), rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨-x, (show -x < 0 from neg_lt_zero.mpr hx), by simp⟩
      rw [hfun, him]
      simpa only [u, v, sub_add_cancel, mul_comm] using
        ratio_image_positive hu huv hc hδ hanti

end D5.S3.Analytic.KummerRatio.Result
