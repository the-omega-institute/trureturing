/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform quadratic cusp remainder and its exact limiting coefficient for the actual arithmetic kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.MeanValue

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
    field_simp
    <;> ring

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
    simpa [K_zero] using K_continuous.continuousAt.tendsto.mono_left (s := 𝓝[>] 0) nhdsWithin_le_nhds
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
      (s := 𝓝[>] 0) nhdsWithin_le_nhds)
    simp only [Real.log_zero, mul_zero] at hm
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    dsimp
    field_simp
  have hh := (((hk.div_const 2).sub hep).add
    ((he.mul_const (Real.log (2 * Real.pi))).add
      (((he.mul hl).add hx).div_const 2))).sub_const (1 / 2 + c)
  have hmass : firstLiMass / 2 - 1 +
      (Real.log (2 * Real.pi) + Real.log 2 / 2) - (1 / 2 + c) = 0 := by
    rw [firstLiMass_split, c, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
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
        (((hasDerivAt_id t).const_mul 2).exp) |>.add_const 1 using 1 <;> dsimp [f, f₁] <;> ring
  have hf₁ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    convert (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).mul
      (((hasDerivAt_id t).neg.div_const 2).exp)).sub
        ((((hasDerivAt_id t).const_mul 2).exp).const_mul 2) using 1 <;> dsimp [f₁, f₂] <;> ring
  have hg (t : ℝ) : HasDerivAt g (g₁ t) t := by
    convert ((hasDerivAt_id t).const_mul 2).mul
      ((((hasDerivAt_id t).const_mul 2).exp).sub_const 1) using 1 <;> dsimp [g, g₁] <;> ring
  have hg₁ (t : ℝ) : HasDerivAt g₁ (g₂ t) t := by
    convert (((((hasDerivAt_id t).const_mul 2).exp).sub_const 1).const_mul 2).add
      (((hasDerivAt_id t).const_mul 4).mul
        (((hasDerivAt_id t).const_mul 2).exp)) using 1 <;> dsimp [g₁, g₂] <;> ring
  have hlim : Tendsto (fun t => f₂ t / g₂ t) (𝓝[>] 0) (𝓝 (-3 / 4)) := by
    have hc : ContinuousAt (fun t => f₂ t / g₂ t) 0 := by
      apply ContinuousAt.div <;> dsimp [f₂, g₂]
      · fun_prop
      · fun_prop
      · norm_num
    simpa [f₂, g₂] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim₁ : Tendsto (fun t => f₁ t / g₁ t) (𝓝[>] 0) (𝓝 (-3 / 4)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf₁) (Eventually.of_forall hg₁) _ _ _ hlim
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      dsimp [g₂]
      positivity
    · simpa [f₁] using (hf₁ 0).continuousAt.tendsto.mono_left (s := 𝓝[>] 0) nhdsWithin_le_nhds
    · simpa [g₁] using (hg₁ 0).continuousAt.tendsto.mono_left (s := 𝓝[>] 0) nhdsWithin_le_nhds
  have hlim₀ : Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 (-3 / 4)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf) (Eventually.of_forall hg) _ _ _ hlim₁
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      have he : 0 < Real.exp (2 * t) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
      exact (show 0 < g₁ t by dsimp [g₁]; positivity).ne'
    · simpa [f] using (hf 0).continuousAt.tendsto.mono_left (s := 𝓝[>] 0) nhdsWithin_le_nhds
    · simpa [g] using (hg 0).continuousAt.tendsto.mono_left (s := 𝓝[>] 0) nhdsWithin_le_nhds
  apply hlim₀.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have he : Real.exp (2 * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith : 0 < 2 * t))).ne'
  dsimp [f, g]
  field_simp
  <;> ring

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
