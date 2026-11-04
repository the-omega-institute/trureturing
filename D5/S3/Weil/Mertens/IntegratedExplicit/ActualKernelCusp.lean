/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform quadratic cusp remainder and its exact limiting coefficient for the actual arithmetic kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.MeanValue

/-! Subtracting the logarithmic cusp leaves a bounded curvature with a finite endpoint limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter
open scoped Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp

/-- The linear coefficient after the logarithmic cusp is removed. -/
def c : ℝ := (Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)) / 2

/-- The remainder of the actual kernel after its constant, logarithmic and linear terms. -/
def R (t : ℝ) : ℝ := K t - firstLiMass - (t / 2) * Real.log t - c * t

private def r1 (t : ℝ) : ℝ := D1 t - (Real.log t + 1) / 2 - c

private def r2 (t : ℝ) : ℝ := D2 t - 1 / (2 * t)

private lemma hasDerivAt_R {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt R (r1 t) t := by
  convert (((hasDerivAt_K ht ht2).sub_const firstLiMass).sub
    (((hasDerivAt_id t).div_const 2).mul (Real.hasDerivAt_log ht.ne'))).sub
      ((hasDerivAt_id t).const_mul c) using 1
  · rfl
  · dsimp [r1]
    field_simp [ht.ne']

private lemma hasDerivAt_r1 {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt r1 (r2 t) t := by
  convert ((hasDerivAt_D1 ht ht2).sub
    (((Real.hasDerivAt_log ht.ne').add_const 1).div_const 2)).sub_const c using 1
  · rfl
  · dsimp [r2]
    ring

private lemma R_continuous : Continuous R := by
  have hlog : Continuous (fun t : ℝ => (t / 2) * Real.log t) := by
    convert Real.continuous_mul_log.div_const 2 using 1
    funext t
    ring
  exact ((K_continuous.sub continuous_const).sub hlog).sub (continuous_const.mul continuous_id)

private lemma R_zero : R 0 = 0 := by simp [R, K_zero]

private lemma r1_limit : Tendsto r1 (𝓝[>] 0) (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t / 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (show ContinuousAt (fun t : ℝ => Real.exp (-t / 2)) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hep : Tendsto (fun t : ℝ => Real.exp (t / 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (show ContinuousAt (fun t : ℝ => Real.exp (t / 2)) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hk : Tendsto K (𝓝[>] 0) (𝓝 firstLiMass) := by
    simpa [K_zero] using K_continuous.continuousAt.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
  have hl : Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-(2 * t))) - Real.log t)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have hi := log_argument_ratio_limit.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
    have hh : Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * t))) / t)
        (𝓝[>] 0) (𝓝 2) := by simpa using hi
    have hhlog := hh.log (by norm_num : (2 : ℝ) ≠ 0)
    apply hhlog.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact Real.log_div (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith : -(2 * t) < 0))).ne' ht.ne'
  have hs : Tendsto (fun t : ℝ => (Real.exp (-t / 2) - 1) / t)
      (𝓝[>] 0) (𝓝 (-1 / 2)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ((((hasDerivAt_id (0 : ℝ)).neg.div_const 2).exp).tendsto_slope_zero_right)
  have hx : Tendsto (fun t : ℝ => (Real.exp (-t / 2) - 1) * Real.log t)
      (𝓝[>] 0) (𝓝 0) := by
    have hm := hs.mul (Real.continuous_mul_log.continuousAt.tendsto.mono_left
      (y := 𝓝[>] 0) nhdsWithin_le_nhds)
    simp only [Real.log_zero, mul_zero] at hm
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    field_simp [ht.ne']
  have hh := (((hk.div_const 2).sub hep).add
    ((he.mul_const (Real.log (2 * Real.pi))).add
      (((he.mul hl).add hx).div_const 2))).sub_const (1 / 2 + c)
  have hmass : firstLiMass / 2 - 1 +
      (Real.log (2 * Real.pi) + Real.log 2 / 2) - (1 / 2 + c) = 0 := by
    simp only [firstLiMass_split, c,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    ring
  simp only [one_mul, add_zero] at hh
  rw [hmass] at hh
  convert hh using 1
  funext t
  dsimp [r1, D1]
  ring

/-- The finite part of the singular exponential quotient is minus three quarters. -/
private lemma quotient_finite_part :
    Tendsto (fun t : ℝ => Real.exp (-t / 2) / (Real.exp (2 * t) - 1) - 1 / (2 * t))
      (𝓝[>] 0) (𝓝 (-3 / 4)) := by
  let f := fun t : ℝ => 2 * t * Real.exp (-t / 2) - Real.exp (2 * t) + 1
  let f₁ := fun t : ℝ => (2 - t) * Real.exp (-t / 2) - 2 * Real.exp (2 * t)
  let f₂ := fun t : ℝ => (t / 2 - 2) * Real.exp (-t / 2) - 4 * Real.exp (2 * t)
  let g := fun t : ℝ => 2 * t * (Real.exp (2 * t) - 1)
  let g₁ := fun t : ℝ => 2 * (Real.exp (2 * t) - 1) + 4 * t * Real.exp (2 * t)
  let g₂ := fun t : ℝ => 8 * (1 + t) * Real.exp (2 * t)
  have hf (t : ℝ) : HasDerivAt f (f₁ t) t := by
    convert (((hasDerivAt_id t).const_mul 2).mul
      (((hasDerivAt_id t).neg.div_const 2).exp)).sub
        (((hasDerivAt_id t).const_mul 2).exp) |>.add_const 1 using 1 <;> (try funext u) <;> dsimp [f, f₁] <;> ring
  have hf₁ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    convert (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).mul
      (((hasDerivAt_id t).neg.div_const 2).exp)).sub
        ((((hasDerivAt_id t).const_mul 2).exp).const_mul 2) using 1 <;> (try funext u) <;> dsimp [f₁, f₂] <;> ring
  have hg (t : ℝ) : HasDerivAt g (g₁ t) t := by
    convert ((hasDerivAt_id t).const_mul 2).mul
      ((((hasDerivAt_id t).const_mul 2).exp).sub_const 1) using 1 <;> (try funext u) <;> dsimp [g, g₁] <;> ring
  have hg₁ (t : ℝ) : HasDerivAt g₁ (g₂ t) t := by
    convert (((((hasDerivAt_id t).const_mul 2).exp).sub_const 1).const_mul 2).add
      (((hasDerivAt_id t).const_mul 4).mul
        (((hasDerivAt_id t).const_mul 2).exp)) using 1 <;> (try funext u) <;> dsimp [g₁, g₂] <;> ring
  have hlim : Tendsto (fun t => f₂ t / g₂ t) (𝓝[>] 0) (𝓝 (-3 / 4)) := by
    have hc : ContinuousAt (fun t => f₂ t / g₂ t) 0 := by
      apply ContinuousAt.div <;> dsimp [f₂, g₂]
      · fun_prop
      · fun_prop
      · norm_num
    convert hc.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds using 1 <;>
      norm_num [f₂, g₂]
  have hlim₁ : Tendsto (fun t => f₁ t / g₁ t) (𝓝[>] 0) (𝓝 (-3 / 4)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf₁) (Eventually.of_forall hg₁) _ _ _ hlim
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      dsimp [g₂]
      positivity
    · simpa [f₁] using (hf₁ 0).continuousAt.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
    · simpa [g₁] using (hg₁ 0).continuousAt.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
  have hlim₀ : Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 (-3 / 4)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf) (Eventually.of_forall hg) _ _ _ hlim₁
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      have he : 0 < Real.exp (2 * t) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
      exact (show 0 < g₁ t by dsimp [g₁]; positivity).ne'
    · simpa [f] using (hf 0).continuousAt.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
    · simpa [g] using (hg 0).continuousAt.tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
  apply hlim₀.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have he : Real.exp (2 * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith : 0 < 2 * t))).ne'
  dsimp [f, g]
  field_simp [ht.ne', he]
  <;> ring


private lemma r2_limit :
    Tendsto r2 (𝓝[>] 0) (𝓝 ((firstLiMass - 7) / 4)) := by
  have hk : Tendsto K (𝓝[>] 0) (𝓝 firstLiMass) := by
    simpa [K_zero] using K_continuous.continuousAt.tendsto.mono_left
      (y := 𝓝[>] 0) nhdsWithin_le_nhds
  have he : Tendsto (fun t : ℝ => Real.exp (t / 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (show ContinuousAt (fun t : ℝ => Real.exp (t / 2)) 0 by
      fun_prop).tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
  have h := ((hk.div_const 4).sub he).add quotient_finite_part
  have hc : firstLiMass / 4 - 1 + (-3 / 4) = (firstLiMass - 7) / 4 := by ring
  rw [hc] at h
  convert h using 1
  funext t
  dsimp [r2, D2]
  ring

/-- The exact quadratic coefficient after removal of the logarithmic and linear cusp terms. -/
theorem cusp_quadratic_limit :
    Tendsto (fun t : ℝ => R t / t ^ 2) (𝓝[>] 0)
      (𝓝 ((firstLiMass - 7) / 8)) := by
  have hw : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < Real.log 2 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2)))] with t ht ht2
    exact ⟨ht, ht2⟩
  have hfirst : Tendsto (fun t : ℝ => r1 t / (2 * t)) (𝓝[>] 0)
      (𝓝 ((firstLiMass - 7) / 8)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (hw.mono fun t ht => hasDerivAt_r1 ht.1 ht.2)
      (Eventually.of_forall fun t => (hasDerivAt_id t).const_mul 2)
      (Eventually.of_forall fun _ => by norm_num) r1_limit _ _
    · simpa using (show ContinuousAt (fun t : ℝ => 2 * t) 0 by
        fun_prop).tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds
    · have hc : (firstLiMass - 7) / 4 / 2 = (firstLiMass - 7) / 8 := by ring
      simpa only [hc, mul_one] using r2_limit.div_const 2
  apply HasDerivAt.lhopital_zero_nhdsGT (f' := r1) (g' := fun t : ℝ => 2 * t)
    (hw.mono fun t ht => hasDerivAt_R ht.1 ht.2)
    (Eventually.of_forall fun t => by
      convert (hasDerivAt_id t).pow 2 using 1 <;>
        (try funext u) <;> simp only [Pi.pow_apply, id_eq] <;> ring)
    (hw.mono fun t ht => (mul_pos (by norm_num : (0 : ℝ) < 2) ht.1).ne') _ _ hfirst
  · simpa [R_zero] using R_continuous.continuousAt.tendsto.mono_left
      (y := 𝓝[>] 0) nhdsWithin_le_nhds
  · simpa using (show ContinuousAt (fun t : ℝ => t ^ 2) 0 by
      fun_prop).tendsto.mono_left (y := 𝓝[>] 0) nhdsWithin_le_nhds


private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

private lemma exp_half_bounds {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    1 ≤ Real.exp (t / 2) ∧ Real.exp (t / 2) ≤ 2 := by
  refine ⟨Real.one_le_exp (by linarith), ?_⟩
  have h := Real.exp_bound_div_one_sub_of_interval
    (show 0 ≤ t / 2 by linarith) (show t / 2 < 1 by linarith)
  have hh : 1 / (1 - t / 2) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - t / 2)).mpr
    linarith
  exact h.trans hh

private lemma K_bounds {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    -3 ≤ K t ∧ K t ≤ 5 := by
  have hL : 0 ≤ Real.log (2 * Real.pi) ∧ Real.log (2 * Real.pi) ≤ 3 := by
    constructor
    · exact Real.log_nonneg (by linarith [Real.two_le_pi])
    · calc
        Real.log (2 * Real.pi) ≤ Real.log ((2 : ℝ) ^ 3) :=
          Real.log_le_log (by positivity) (by nlinarith [Real.pi_lt_four])
        _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hT₀ := trivialT_nonneg ht.le
  have hT₁ : trivialT t ≤ 1 := by
    have := trivialT_le_mass ht.le
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hA : 0 ≤ 1 + Real.eulerMascheroniConstant - t ∧
      1 + Real.eulerMascheroniConstant - t ≤ 2 := by
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant,
      Real.eulerMascheroniConstant_lt_two_thirds]
  have hp := exp_half_bounds ht ht'
  have hm₀ := (Real.exp_pos (-t / 2)).le
  have hm₁ : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfirst₀ := mul_nonneg (Real.exp_nonneg (t / 2)) hA.1
  have hfirst₁ : Real.exp (t / 2) * (1 + Real.eulerMascheroniConstant - t) ≤ 4 :=
    (mul_le_mul hp.2 hA.2 hA.1 (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num)
  have hcorr₀ : -3 ≤ Real.exp (-t / 2) * (trivialT t - Real.log (2 * Real.pi)) := by
    nlinarith [mul_nonneg hm₀ hT₀,
      mul_le_mul_of_nonneg_left hL.2 hm₀]
  have hcorr₁ : Real.exp (-t / 2) * (trivialT t - Real.log (2 * Real.pi)) ≤ 1 := by
    nlinarith [mul_nonneg hm₀ hL.1, mul_le_mul_of_nonneg_left hT₁ hm₀]
  have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hident : K t = Real.exp (t / 2) * (1 + Real.eulerMascheroniConstant - t) +
      Real.exp (-t / 2) * (trivialT t - Real.log (2 * Real.pi)) := by
    rw [K_eq_local ht.le (ht'.trans_lt half_lt_log_two)]
    calc
      _ = (Real.exp (-t / 2) * Real.exp t) * (1 + Real.eulerMascheroniConstant - t) +
          Real.exp (-t / 2) * (trivialT t - Real.log (2 * Real.pi)) := by ring
      _ = _ := by rw [he]
  rw [hident]
  constructor <;> linarith

private lemma reciprocal_exp_bounds {x : ℝ} (hx : 0 < x) :
    -1 ≤ 1 / (Real.exp x - 1) - 1 / x ∧
      1 / (Real.exp x - 1) - 1 / x ≤ 0 := by
  have he : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  have htan := Real.add_one_le_exp x
  have hneg := Real.one_sub_le_exp_neg x
  have hprod := mul_le_mul_of_nonneg_left hneg (Real.exp_nonneg x)
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hprod
  have hid : 1 / (Real.exp x - 1) - 1 / x =
      (x - (Real.exp x - 1)) / ((Real.exp x - 1) * x) := by
    field_simp [he.ne', hx.ne']
  constructor
  · rw [hid]
    apply (le_div_iff₀ (mul_pos he hx)).mpr
    nlinarith
  · have h := one_div_le_one_div_of_le hx (by linarith : x ≤ Real.exp x - 1)
    linarith

private lemma quotient_bounds {t : ℝ} (ht : 0 < t) :
    -5 / 4 ≤ Real.exp (-t / 2) / (Real.exp (2 * t) - 1) - 1 / (2 * t) ∧
      Real.exp (-t / 2) / (Real.exp (2 * t) - 1) - 1 / (2 * t) ≤ 0 := by
  have hq := reciprocal_exp_bounds (show 0 < 2 * t by linarith)
  have hm₀ := Real.exp_nonneg (-t / 2)
  have hm₁ : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have htan : 1 - t / 2 ≤ Real.exp (-t / 2) := by
    simpa only [neg_div] using Real.one_sub_le_exp_neg (t / 2)
  have hfrac : -1 / 4 ≤ (Real.exp (-t / 2) - 1) / (2 * t) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * t)).mpr
    linarith
  have hfrac' : (Real.exp (-t / 2) - 1) / (2 * t) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hq.1 hm₀
  have hmul' := mul_nonpos_of_nonneg_of_nonpos hm₀ hq.2
  have hid : Real.exp (-t / 2) / (Real.exp (2 * t) - 1) - 1 / (2 * t) =
      Real.exp (-t / 2) * (1 / (Real.exp (2 * t) - 1) - 1 / (2 * t)) +
        (Real.exp (-t / 2) - 1) / (2 * t) := by ring
  rw [hid]
  constructor <;> nlinarith

private lemma r2_bound {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |r2 t| ≤ 4 := by
  have hk := K_bounds ht ht'
  have he := exp_half_bounds ht ht'
  have hq := quotient_bounds ht
  rw [abs_le]
  dsimp [r2, D2]
  constructor <;> linarith

private lemma r1_bound {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |r1 t| ≤ 4 * t := by
  have hlim : Tendsto (fun ε : ℝ => |r1 t - r1 ε|) (𝓝[>] 0) (𝓝 |r1 t|) := by
    simpa using (tendsto_const_nhds.sub r1_limit).abs
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht)] with ε hε hεt
  change 0 < ε at hε
  have hd (x : ℝ) (hx : x ∈ Icc ε t) :
      HasDerivWithinAt r1 (r2 x) (Icc ε t) x :=
    (hasDerivAt_r1 (hε.trans_le hx.1)
      ((hx.2.trans ht').trans_lt half_lt_log_two)).hasDerivWithinAt
  have hb (x : ℝ) (hx : x ∈ Ico ε t) : ‖r2 x‖ ≤ 4 := by
    rw [Real.norm_eq_abs]
    exact r2_bound (hε.trans_le hx.1) (hx.2.le.trans ht')
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨hεt.le, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (by linarith)

/-- On the entire explicit half-unit interval the cusp remainder is bounded by twice t squared. -/
theorem cusp_remainder_bound {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |R t| ≤ 2 * t ^ 2 := by
  have hp (x : ℝ) (hx : x ∈ Ioo 0 t) :
      HasDerivAt (fun u : ℝ => 2 * u ^ 2 + R u) (4 * x + r1 x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul 2).add
      (hasDerivAt_R hx.1 (hx.2.le.trans ht' |>.trans_lt half_lt_log_two)) using 1 <;>
        (try funext u) <;> simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, id_eq] <;> ring
  have hm (x : ℝ) (hx : x ∈ Ioo 0 t) :
      HasDerivAt (fun u : ℝ => 2 * u ^ 2 - R u) (4 * x - r1 x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul 2).sub
      (hasDerivAt_R hx.1 (hx.2.le.trans ht' |>.trans_lt half_lt_log_two)) using 1 <;>
        (try funext u) <;> simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq] <;> ring
  have hmono_add : MonotoneOn (fun u : ℝ => 2 * u ^ 2 + R u) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (f := fun u : ℝ => 2 * u ^ 2 + R u)
      (convex_Icc 0 t)
      ((continuous_const.mul (continuous_id.pow 2)).add R_continuous).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hp x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hp x hx).deriv]
      have h := (abs_le.mp (r1_bound hx.1 (hx.2.le.trans ht'))).1
      linarith
  have hmono_sub : MonotoneOn (fun u : ℝ => 2 * u ^ 2 - R u) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (f := fun u : ℝ => 2 * u ^ 2 - R u)
      (convex_Icc 0 t)
      ((continuous_const.mul (continuous_id.pow 2)).sub R_continuous).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hm x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hm x hx).deriv]
      have h := (abs_le.mp (r1_bound hx.1 (hx.2.le.trans ht'))).2
      linarith
  have hp₀ := hmono_add ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
  have hm₀ := hmono_sub ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
  simp only [R_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add, sub_zero] at hp₀ hm₀
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms cusp_remainder_bound

#print axioms cusp_quadratic_limit
#print axioms K_eq_local
#print axioms K_zero
#print axioms K_continuous
#print axioms hasDerivAt_K
#print axioms hasDerivAt_D1
#print axioms log_argument_ratio_limit
#print axioms D1_atBot
end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
