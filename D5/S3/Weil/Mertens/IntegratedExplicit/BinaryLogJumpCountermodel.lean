/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/BinaryLogJumpCountermodel
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/BinaryLogJumpCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exact binary log-jump count realizes negative tail mass at power one sixth. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! An oscillatory continuum count and its discretization by floor increments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel

private def phase (x : ℝ) : ℝ := x ^ (1 / 6 : ℝ)

def count (x : ℝ) : ℝ :=
  x - x ^ (1 / 2 : ℝ) +
    (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) * Real.sin (phase x) -
    (1 / 6 : ℝ) * x ^ (5 / 6 : ℝ) * Real.cos (phase x)

private def countSlope (x : ℝ) : ℝ :=
  1 - (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) +
    (2 / 9 : ℝ) * x ^ (-1 / 3 : ℝ) * Real.sin (phase x) -
    (1 / 12 : ℝ) * x ^ (-1 / 6 : ℝ) * Real.cos (phase x) +
    (1 / 36 : ℝ) * Real.sin (phase x)

private def tailKernel (x : ℝ) : ℝ := (count x - x) / x ^ 2

private def integratedTail (x : ℝ) : ℝ := ∫ t in Ioi x, tailKernel t

private def modelTail (x : ℝ) : ℝ :=
  -2 * x ^ (-1 / 2 : ℝ) + x ^ (-1 / 3 : ℝ) * Real.sin (phase x)

private lemma hasDerivAt_power {x : ℝ} (hx : 0 < x) (p e : ℝ) (he : p - 1 = e) :
    HasDerivAt (fun y : ℝ => y ^ p) (p * x ^ e) x := by
  rw [← he]
  exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')

private lemma rpow_product {x p r s : ℝ} (hx : 0 < x) (h : p + r = s) :
    x ^ p * x ^ r = x ^ s := by
  rw [← Real.rpow_add hx, h]

private lemma rpow_div_sq {x p e : ℝ} (hx : 0 < x) (he : p - 2 = e) :
    x ^ p / x ^ 2 = x ^ e := by
  rw [← Real.rpow_two, ← Real.rpow_sub hx, he]

private lemma hasDerivAt_phase {x : ℝ} (hx : 0 < x) :
    HasDerivAt phase ((1 / 6 : ℝ) * x ^ (-5 / 6 : ℝ)) x :=
  hasDerivAt_power hx (1 / 6) (-5 / 6) (by norm_num)

private theorem hasDerivAt_count {x : ℝ} (hx : 0 < x) : HasDerivAt count (countSlope x) x := by
  have hhalf := hasDerivAt_power hx (1 / 2) (-1 / 2) (by norm_num)
  have htwo := hasDerivAt_power hx (2 / 3) (-1 / 3) (by norm_num)
  have hfive := hasDerivAt_power hx (5 / 6) (-1 / 6) (by norm_num)
  have hu := hasDerivAt_phase hx
  have h := (((hasDerivAt_id x).sub hhalf).add ((htwo.mul hu.sin).const_mul (1 / 3))).sub
    ((hfive.mul hu.cos).const_mul (1 / 6))
  have heq :
      ((id - (fun y : ℝ => y ^ (1 / 2 : ℝ))) +
        (fun y => (1 / 3 : ℝ) * ((fun y : ℝ => y ^ (2 / 3 : ℝ)) *
          (fun y => Real.sin (phase y))) y)) -
        (fun y => (1 / 6 : ℝ) * ((fun y : ℝ => y ^ (5 / 6 : ℝ)) *
          (fun y => Real.cos (phase y))) y) = count := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, count]
    ring
  rw [heq] at h
  refine h.congr_deriv ?_
  have hcos := rpow_product hx (show (2 / 3 : ℝ) + (-5 / 6) = -1 / 6 by norm_num)
  have hsin : x ^ (5 / 6 : ℝ) * x ^ (-5 / 6 : ℝ) = 1 := by
    rw [rpow_product hx (show (5 / 6 : ℝ) + (-5 / 6) = 0 by norm_num), Real.rpow_zero]
  unfold countSlope
  linear_combination (1 / 18 : ℝ) * Real.cos (phase x) * hcos +
    (1 / 36 : ℝ) * Real.sin (phase x) * hsin

private lemma rpow_le_one {x e : ℝ} (hx : 1 ≤ x) (he : e ≤ 0) : x ^ e ≤ 1 := by
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx he

private theorem countSlope_bounds {x : ℝ} (hx : 1 ≤ x) :
    (1 / 6 : ℝ) ≤ countSlope x ∧ countSlope x ≤ 4 / 3 := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hhalf := rpow_le_one hx (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  have hhalf₀ := Real.rpow_nonneg hx₀ (-1 / 2)
  have hthird := rpow_le_one hx (show (-1 / 3 : ℝ) ≤ 0 by norm_num)
  have hthird₀ := Real.rpow_nonneg hx₀ (-1 / 3)
  have hsixth := rpow_le_one hx (show (-1 / 6 : ℝ) ≤ 0 by norm_num)
  have hsixth₀ := Real.rpow_nonneg hx₀ (-1 / 6)
  have hsinLower := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (phase x)) hthird₀
  have hsinUpper := mul_le_mul_of_nonneg_left (Real.sin_le_one (phase x)) hthird₀
  have hcosLower := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (phase x)) hsixth₀
  have hcosUpper := mul_le_mul_of_nonneg_left (Real.cos_le_one (phase x)) hsixth₀
  unfold countSlope
  constructor
  · linarith only [hhalf, hthird, hsixth, hsinLower, hcosUpper, Real.neg_one_le_sin (phase x)]
  · linarith only [hhalf₀, hthird, hsixth, hsinUpper, hcosLower, Real.sin_le_one (phase x)]

private theorem strictMonoOn_count : StrictMonoOn count (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ))
  · intro x hx
    exact (hasDerivAt_count (zero_lt_one.trans_le (mem_Ici.mp hx))).continuousAt.continuousWithinAt
  · intro x hx
    have hx₁ : 1 ≤ x := mem_Ici.mp (interior_subset hx)
    rw [(hasDerivAt_count (zero_lt_one.trans_le hx₁)).deriv]
    exact (by norm_num : (0 : ℝ) < 1 / 6).trans_le (countSlope_bounds hx₁).1

private theorem count_pos {x : ℝ} (hx : 1 ≤ x) : 0 < count x := by
  have h₁ : 0 < count 1 := by
    have hs := Real.sin_gt_sub_cube (x := 1) zero_lt_one
    have hc := Real.cos_le_one (1 : ℝ)
    simp only [count, phase, Real.one_rpow]
    linarith only [hs, hc]
  have hm : count 1 ≤ count x :=
    strictMonoOn_count.monotoneOn self_mem_Ici (mem_Ici.mpr hx) hx
  exact h₁.trans_le hm

private theorem count_error {x : ℝ} (hx : 1 ≤ x) :
    |count x - x| ≤ (3 / 2 : ℝ) * x ^ (5 / 6 : ℝ) := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hhalf : x ^ (1 / 2 : ℝ) ≤ x ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have htwo : x ^ (2 / 3 : ℝ) ≤ x ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hs : |x ^ (2 / 3 : ℝ) * Real.sin (phase x)| ≤ x ^ (5 / 6 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx₀ (2 / 3))]
    exact (mul_le_of_le_one_right (Real.rpow_nonneg hx₀ _) (Real.abs_sin_le_one _)).trans htwo
  have hc : |x ^ (5 / 6 : ℝ) * Real.cos (phase x)| ≤ x ^ (5 / 6 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx₀ (5 / 6))]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hx₀ _) (Real.abs_cos_le_one _)
  have habs := abs_add_le
    (-x ^ (1 / 2 : ℝ) + (1 / 3 : ℝ) * (x ^ (2 / 3 : ℝ) * Real.sin (phase x)))
    (-(1 / 6 : ℝ) * (x ^ (5 / 6 : ℝ) * Real.cos (phase x)))
  have hsum := abs_add_le (-x ^ (1 / 2 : ℝ))
    ((1 / 3 : ℝ) * (x ^ (2 / 3 : ℝ) * Real.sin (phase x)))
  rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg hx₀ (1 / 2)), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hsum
  have hterm :
      |-(1 / 6 : ℝ) * (x ^ (5 / 6 : ℝ) * Real.cos (phase x))| =
        (1 / 6 : ℝ) * |x ^ (5 / 6 : ℝ) * Real.cos (phase x)| := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rw [hterm] at habs
  rw [show count x - x =
    (-x ^ (1 / 2 : ℝ) + (1 / 3 : ℝ) * (x ^ (2 / 3 : ℝ) * Real.sin (phase x))) +
    (-(1 / 6 : ℝ) * (x ^ (5 / 6 : ℝ) * Real.cos (phase x))) by
      unfold count
      ring]
  linarith only [habs, hsum, hhalf, hs, hc]

private lemma tendsto_rpow_zero {p : ℝ} (hp : p < 0) :
    Tendsto (fun x : ℝ => x ^ p) atTop (𝓝 0) := by
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hp)

private theorem count_pnt : Tendsto (fun x : ℝ => count x / x) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (g := fun x : ℝ => (3 / 2 : ℝ) * x ^ (-1 / 6 : ℝ))
    (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx₀ : 0 < x := zero_lt_one.trans_le hx
    have hpow : x ^ (5 / 6 : ℝ) / x = x ^ (-1 / 6 : ℝ) := by
      rw [← Real.rpow_sub_one hx₀.ne', show (5 / 6 : ℝ) - 1 = -1 / 6 by norm_num]
    have hratio : count x / x - 1 = (count x - x) / x := by
      rw [sub_div, div_self hx₀.ne']
    rw [Real.norm_eq_abs, hratio, abs_div, abs_of_pos hx₀]
    calc
      _ ≤ ((3 / 2 : ℝ) * x ^ (5 / 6 : ℝ)) / x :=
        div_le_div_of_nonneg_right (count_error hx) hx₀.le
      _ = (3 / 2 : ℝ) * x ^ (-1 / 6 : ℝ) := by rw [mul_div_assoc, hpow]
  · simpa only [mul_zero] using (tendsto_rpow_zero (by norm_num : (-1 / 6 : ℝ) < 0)).const_mul
      (3 / 2 : ℝ)

private lemma tailKernel_formula {x : ℝ} (hx : 0 < x) :
    tailKernel x = -x ^ (-3 / 2 : ℝ) +
      (1 / 3 : ℝ) * x ^ (-4 / 3 : ℝ) * Real.sin (phase x) -
      (1 / 6 : ℝ) * x ^ (-7 / 6 : ℝ) * Real.cos (phase x) := by
  calc
    tailKernel x =
        -(x ^ (1 / 2 : ℝ) / x ^ 2) +
        (1 / 3 : ℝ) * (x ^ (2 / 3 : ℝ) / x ^ 2) * Real.sin (phase x) -
        (1 / 6 : ℝ) * (x ^ (5 / 6 : ℝ) / x ^ 2) * Real.cos (phase x) := by
          unfold tailKernel count
          simp only [div_eq_mul_inv]
          ring
    _ = _ := by
      rw [rpow_div_sq hx (show (1 / 2 : ℝ) - 2 = -3 / 2 by norm_num),
        rpow_div_sq hx (show (2 / 3 : ℝ) - 2 = -4 / 3 by norm_num),
        rpow_div_sq hx (show (5 / 6 : ℝ) - 2 = -7 / 6 by norm_num)]

private lemma hasDerivAt_modelTail {x : ℝ} (hx : 0 < x) :
    HasDerivAt modelTail (-tailKernel x) x := by
  have hhalf := hasDerivAt_power hx (-1 / 2) (-3 / 2) (by norm_num)
  have hthird := hasDerivAt_power hx (-1 / 3) (-4 / 3) (by norm_num)
  have hu := hasDerivAt_phase hx
  have h := (hhalf.const_mul (-2)).add (hthird.mul hu.sin)
  refine h.congr_deriv ?_
  rw [tailKernel_formula hx]
  have hcos := rpow_product hx (show (-1 / 3 : ℝ) + (-5 / 6) = -7 / 6 by norm_num)
  linear_combination (1 / 6 : ℝ) * Real.cos (phase x) * hcos

private lemma modelTail_tendsto_zero : Tendsto modelTail atTop (𝓝 0) := by
  have hhalf := (tendsto_rpow_zero (by norm_num : (-1 / 2 : ℝ) < 0)).const_mul (-2 : ℝ)
  have hsin : Tendsto (fun x : ℝ => x ^ (-1 / 3 : ℝ) * Real.sin (phase x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_rpow_zero (by norm_num : (-1 / 3 : ℝ) < 0))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx (-1 / 3))]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hx _) (Real.abs_sin_le_one _)
  have heq : (fun x : ℝ => -2 * x ^ (-1 / 2 : ℝ) +
      x ^ (-1 / 3 : ℝ) * Real.sin (phase x)) = modelTail := rfl
  simpa only [mul_zero, zero_add, heq] using hhalf.add hsin

private theorem integrableOn_tailKernel {x : ℝ} (hx : 1 ≤ x) : IntegrableOn tailKernel (Ioi x) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hc : ContinuousOn count (Ioi x) := by
    intro t ht
    exact (hasDerivAt_count (hx₀.trans (mem_Ioi.mp ht))).continuousAt.continuousWithinAt
  have hk : ContinuousOn tailKernel (Ioi x) :=
    (hc.sub continuousOn_id).div (continuousOn_id.pow 2) (fun t ht =>
      pow_ne_zero 2 (hx₀.trans (mem_Ioi.mp ht)).ne')
  have hmajor : IntegrableOn (fun t : ℝ => (3 / 2 : ℝ) * t ^ (-7 / 6 : ℝ)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-7 / 6 : ℝ) < -1) hx₀).const_mul (3 / 2)
  refine hmajor.mono' (hk.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi x) measurableSet_Ioi] with t ht
  have ht₀ : 0 < t := hx₀.trans (mem_Ioi.mp ht)
  rw [Real.norm_eq_abs, tailKernel, abs_div, abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ ((3 / 2 : ℝ) * t ^ (5 / 6 : ℝ)) / t ^ 2 :=
      div_le_div_of_nonneg_right (count_error (hx.trans (mem_Ioi.mp ht).le)) (sq_nonneg t)
    _ = _ := by
      rw [mul_div_assoc, rpow_div_sq ht₀ (show (5 / 6 : ℝ) - 2 = -7 / 6 by norm_num)]

private theorem integratedTail_eq {x : ℝ} (hx : 1 ≤ x) : integratedTail x = modelTail x := by
  have hd (t : ℝ) (ht : t ∈ Ici x) :
      HasDerivAt (fun y => -modelTail y) (tailKernel t) t := by
    have ht₀ : 0 < t := zero_lt_one.trans_le (hx.trans (mem_Ici.mp ht))
    have heq : (-modelTail) = (fun y => -modelTail y) := rfl
    simpa only [neg_neg, heq] using (hasDerivAt_modelTail ht₀).neg
  simpa only [integratedTail, neg_zero, zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_tailKernel hx) modelTail_tendsto_zero.neg

private def signedMass (A B : ℝ) : ℝ := ∫ x in A..B, integratedTail x / Real.sqrt x

private def negativeMass (A B : ℝ) : ℝ := ∫ x in A..B, max (-integratedTail x) 0 / Real.sqrt x

private lemma continuousOn_integratedTail : ContinuousOn integratedTail (Ici 1) := by
  have hc : ContinuousOn modelTail (Ici 1) := by
    intro x hx
    exact (hasDerivAt_modelTail (zero_lt_one.trans_le (mem_Ici.mp hx))).continuousAt.continuousWithinAt
  exact hc.congr (fun _ hx => integratedTail_eq (mem_Ici.mp hx))

private lemma interval_subset_tailDomain {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    uIcc A B ⊆ Ici 1 := by
  rw [uIcc_of_le hAB]
  exact fun _ hx => mem_Ici.mpr (hA.trans (mem_Icc.mp hx).1)

private def signedPrimitive (x : ℝ) : ℝ := -2 * Real.log x - 6 * Real.cos (phase x)

private lemma modelTail_div_sqrt {x : ℝ} (hx : 0 < x) :
    modelTail x / Real.sqrt x = -2 * x⁻¹ + x ^ (-5 / 6 : ℝ) * Real.sin (phase x) := by
  have hfirst : x ^ (-1 / 2 : ℝ) / x ^ (1 / 2 : ℝ) = x⁻¹ := by
    rw [← Real.rpow_sub hx, show (-1 / 2 : ℝ) - 1 / 2 = -(1 : ℝ) by norm_num,
      Real.rpow_neg hx.le, Real.rpow_one]
  have hsecond : x ^ (-1 / 3 : ℝ) / x ^ (1 / 2 : ℝ) = x ^ (-5 / 6 : ℝ) := by
    rw [← Real.rpow_sub hx, show (-1 / 3 : ℝ) - 1 / 2 = -5 / 6 by norm_num]
  rw [Real.sqrt_eq_rpow]
  calc
    modelTail x / x ^ (1 / 2 : ℝ) =
        -2 * (x ^ (-1 / 2 : ℝ) / x ^ (1 / 2 : ℝ)) +
        (x ^ (-1 / 3 : ℝ) / x ^ (1 / 2 : ℝ)) * Real.sin (phase x) := by
          unfold modelTail
          simp only [div_eq_mul_inv]
          ring
    _ = _ := by rw [hfirst, hsecond]

private lemma hasDerivAt_signedPrimitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt signedPrimitive (modelTail x / Real.sqrt x) x := by
  have h := ((Real.hasDerivAt_log hx.ne').const_mul (-2)).sub
    ((hasDerivAt_phase hx).cos.const_mul 6)
  refine h.congr_deriv ?_
  rw [modelTail_div_sqrt hx]
  ring

private theorem signedMass_eq {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    signedMass A B = -2 * Real.log (B / A) +
      6 * (Real.cos (phase A) - Real.cos (phase B)) := by
  have hsub := interval_subset_tailDomain hA hAB
  have hc : ContinuousOn (fun x => integratedTail x / Real.sqrt x) (uIcc A B) :=
    (continuousOn_integratedTail.mono hsub).div (Real.continuous_sqrt.continuousOn)
      (fun x hx => (Real.sqrt_pos.2 (zero_lt_one.trans_le (mem_Ici.mp (hsub hx)))).ne')
  have hFTC : signedMass A B = signedPrimitive B - signedPrimitive A := by
    unfold signedMass
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hc.intervalIntegrable
    intro x hx
    have hx₁ := mem_Ici.mp (hsub hx)
    rw [integratedTail_eq hx₁]
    exact hasDerivAt_signedPrimitive (zero_lt_one.trans_le hx₁)
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hB₀ : 0 < B := hA₀.trans_le hAB
  rw [hFTC, Real.log_div hB₀.ne' hA₀.ne']
  unfold signedPrimitive
  ring

private theorem signedMass_bound {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    |signedMass A B + 2 * Real.log (B / A)| ≤ 12 := by
  rw [signedMass_eq hA hAB]
  apply abs_le.mpr
  constructor <;> linarith only [Real.neg_one_le_cos (phase A), Real.cos_le_one (phase A),
    Real.neg_one_le_cos (phase B), Real.cos_le_one (phase B)]

private def lowerDensity (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * x ^ (-5 / 6 : ℝ) * (Real.sin (phase x) ^ 2 - Real.sin (phase x))

private def lowerPrimitive (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * phase x - (3 / 4 : ℝ) * Real.sin (2 * phase x) + 3 * Real.cos (phase x)

private lemma hasDerivAt_lowerPrimitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt lowerPrimitive (lowerDensity x) x := by
  have hu := hasDerivAt_phase hx
  have h := ((hu.const_mul (3 / 2)).sub ((hu.const_mul 2).sin.const_mul (3 / 4))).add
    (hu.cos.const_mul 3)
  refine h.congr_deriv ?_
  unfold lowerDensity
  rw [Real.sin_sq_eq_half_sub]
  ring

private lemma lowerDensity_le {x : ℝ} (hx : 1 ≤ x) :
    lowerDensity x ≤ max (-integratedTail x) 0 / Real.sqrt x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hsqrt := Real.sqrt_pos.2 hx₀
  rw [integratedTail_eq hx]
  let s := Real.sin (phase x)
  have hsUpper : s ≤ 1 := Real.sin_le_one (phase x)
  have hsLower : -1 ≤ s := Real.neg_one_le_sin (phase x)
  have hweight : 0 ≤ (1 / 2 : ℝ) * x ^ (-5 / 6 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hx₀.le _)
  change (1 / 2 : ℝ) * x ^ (-5 / 6 : ℝ) * (s ^ 2 - s) ≤
    max (-modelTail x) 0 / Real.sqrt x
  by_cases hs : 0 ≤ s
  · have hsFactor := mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hsUpper)
    have hsSquare : s ^ 2 - s ≤ 0 := by nlinarith only [hsFactor]
    exact (mul_nonpos_of_nonneg_of_nonpos hweight hsSquare).trans
      (div_nonneg (le_max_right _ _) hsqrt.le)
  · have hsFactor := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs)
      (show 0 ≤ s + 1 by linarith only [hsLower])
    have hsSquare : s ^ 2 - s ≤ -2 * s := by nlinarith only [hsFactor]
    have hratio : x ^ (-1 / 3 : ℝ) / x ^ (1 / 2 : ℝ) = x ^ (-5 / 6 : ℝ) := by
      rw [← Real.rpow_sub hx₀, show (-1 / 3 : ℝ) - 1 / 2 = -5 / 6 by norm_num]
    have htail : -(x ^ (-1 / 3 : ℝ) * s) ≤ max (-modelTail x) 0 := by
      apply le_trans ?_ (le_max_left _ _)
      dsimp only [modelTail, s]
      linarith only [Real.rpow_nonneg hx₀.le (-1 / 2)]
    calc
      _ ≤ (1 / 2 : ℝ) * x ^ (-5 / 6 : ℝ) * (-2 * s) :=
        mul_le_mul_of_nonneg_left hsSquare hweight
      _ = -(x ^ (-1 / 3 : ℝ) * s) / Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, ← hratio]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right htail hsqrt.le

private theorem negativeMass_ge {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (3 / 2 : ℝ) * (phase B - phase A) - 15 / 2 ≤ negativeMass A B := by
  have hsub := interval_subset_tailDomain hA hAB
  have hpos (x : ℝ) (hx : x ∈ uIcc A B) : 0 < x :=
    zero_lt_one.trans_le (mem_Ici.mp (hsub hx))
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-5 / 6 : ℝ)) (uIcc A B) :=
    fun x hx => (hasDerivAt_power (hpos x hx) (-5 / 6) (-11 / 6) (by norm_num)).continuousAt.continuousWithinAt
  have hsin : ContinuousOn (fun x => Real.sin (phase x)) (uIcc A B) :=
    fun x hx => (hasDerivAt_phase (hpos x hx)).sin.continuousAt.continuousWithinAt
  have hlower : ContinuousOn lowerDensity (uIcc A B) :=
    (continuousOn_const.mul hpow).mul ((hsin.pow 2).sub hsin)
  have hnegative : ContinuousOn (fun x => max (-integratedTail x) 0 / Real.sqrt x)
      (uIcc A B) :=
    ((continuousOn_integratedTail.mono hsub).neg.sup continuousOn_const).div
      (Real.continuous_sqrt.continuousOn) (fun x hx => (Real.sqrt_pos.2 (hpos x hx)).ne')
  have hcomparison : (∫ x in A..B, lowerDensity x) ≤ negativeMass A B := by
    unfold negativeMass
    apply intervalIntegral.integral_mono_on hAB hlower.intervalIntegrable hnegative.intervalIntegrable
    intro x hx
    exact lowerDensity_le (hA.trans (mem_Icc.mp hx).1)
  have hFTC : (∫ x in A..B, lowerDensity x) = lowerPrimitive B - lowerPrimitive A :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_lowerPrimitive (hpos x hx)) hlower.intervalIntegrable
  rw [hFTC] at hcomparison
  unfold lowerPrimitive at hcomparison
  linarith only [hcomparison, Real.neg_one_le_sin (2 * phase A), Real.sin_le_one (2 * phase B),
    Real.cos_le_one (phase A), Real.neg_one_le_cos (phase B)]

private theorem negativeMass_power_window {b : ℝ} (hb : 1 < b) :
    ∀ᶠ Y : ℝ in atTop, (1 / 2 : ℝ) * Y ^ (b / 6) ≤ negativeMass Y (Y ^ b) := by
  have hsmall : ∀ᶠ Y : ℝ in atTop, Y ^ ((1 - b) / 6) ≤ (1 / 3 : ℝ) :=
    (tendsto_rpow_zero (show (1 - b) / 6 < 0 by linarith)).eventually_le_const (by norm_num)
  have hlarge : ∀ᶠ Y : ℝ in atTop, (15 : ℝ) ≤ Y ^ (b / 6) :=
    (tendsto_rpow_atTop (show 0 < b / 6 by linarith)).eventually_ge_atTop 15
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hlarge] with Y hY hsmallY hlargeY
  have hY₀ := zero_lt_one.trans_le hY
  have hwindow : Y ≤ Y ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY hb.le
  have hB : phase (Y ^ b) = Y ^ (b / 6) := by
    unfold phase
    rw [← Real.rpow_mul hY₀.le, show b * (1 / 6 : ℝ) = b / 6 by ring]
  have hA : phase Y = Y ^ ((1 - b) / 6) * Y ^ (b / 6) := by
    unfold phase
    rw [rpow_product hY₀ (show (1 - b) / 6 + b / 6 = 1 / 6 by ring)]
  have hphase : phase Y ≤ (1 / 3 : ℝ) * Y ^ (b / 6) := by
    rw [hA]
    exact mul_le_mul_of_nonneg_right hsmallY (Real.rpow_nonneg hY₀.le _)
  have hmass := negativeMass_ge hY hwindow
  rw [hB] at hmass
  linarith only [hmass, hphase, hlargeY]

/-- The concrete continuum count satisfies both window estimates for its actual tail. -/
private theorem continuumCountermodel :
    StrictMonoOn count (Ici 1) ∧
    (∀ x : ℝ, 1 ≤ x → 0 < count x ∧ |count x - x| ≤ (3 / 2 : ℝ) * x ^ (5 / 6 : ℝ)) ∧
    Tendsto (fun x : ℝ => count x / x) atTop (𝓝 1) ∧
    (∀ x : ℝ, 1 ≤ x → IntegrableOn tailKernel (Ioi x) ∧ integratedTail x = modelTail x) ∧
    (∀ A B : ℝ, 1 ≤ A → A ≤ B →
      |signedMass A B + 2 * Real.log (B / A)| ≤ 12 ∧
      (3 / 2 : ℝ) * (B ^ (1 / 6 : ℝ) - A ^ (1 / 6 : ℝ)) - 15 / 2 ≤ negativeMass A B) ∧
    (∀ b : ℝ, 1 < b → ∀ᶠ Y : ℝ in atTop, (1 / 2 : ℝ) * Y ^ (b / 6) ≤
      negativeMass Y (Y ^ b)) :=
  ⟨strictMonoOn_count, fun _ hx => ⟨count_pos hx, count_error hx⟩, count_pnt,
    fun _ hx => ⟨integrableOn_tailKernel hx, integratedTail_eq hx⟩,
    fun _ _ hA hAB => ⟨signedMass_bound hA hAB, negativeMass_ge hA hAB⟩,
    fun _ hb => negativeMass_power_window hb⟩

/-! ## Rounding the counting primitive -/

/-- The primitive of the counting density, anchored at eight. -/
private def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (8 : ℝ)..x, f t / Real.log t

/-- The jump at an integer is the corresponding increment of the rounded primitive. -/
private def coefficient (G : ℝ → ℝ) (n : ℕ) : ℝ :=
  if 9 ≤ n then ((⌊G (n : ℝ)⌋ - ⌊G ((n - 1 : ℕ) : ℝ)⌋ : ℤ) : ℝ) else 0

/-- The exact log-weighted count at a real cutoff. -/
def logCount (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Real.log (n : ℝ) * c n

private def prefixCount (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n

private theorem log_pos_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 0 < Real.log x :=
  Real.log_pos ((by norm_num : (1 : ℝ) < 8).trans_le hx)

private theorem density_continuousOn {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Ici (8 : ℝ))) :
    ContinuousOn (fun t => f t / Real.log t) (Set.Ici (8 : ℝ)) := by
  apply hc.div
  · intro t ht
    exact (Real.continuousAt_log (by linarith [Set.mem_Ici.mp ht])).continuousWithinAt
  · intro t ht
    exact (log_pos_of_eight_le ht).ne'

@[simp] private theorem primitive_at_eight (f : ℝ → ℝ) : primitive f 8 = 0 := by
  simp [primitive]

private theorem primitive_increment {f : ℝ → ℝ}
    (hc : ContinuousOn (fun t => f t / Real.log t) (Set.Ici (8 : ℝ)))
    (hf : ∀ t : ℝ, 8 ≤ t → 0 ≤ f t / Real.log t ∧ f t / Real.log t ≤ 1)
    {x y : ℝ} (hx : 8 ≤ x) (hxy : x ≤ y) :
    0 ≤ primitive f y - primitive f x ∧ primitive f y - primitive f x ≤ y - x := by
  have hint {a b : ℝ} (ha : 8 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t => f t / Real.log t) volume a b :=
    (hc.mono (fun _ ht => ha.trans ht.1)).intervalIntegrable_of_Icc hab
  have hdiff : primitive f y - primitive f x = ∫ t in x..y, f t / Real.log t :=
    intervalIntegral.integral_interval_sub_left (hint le_rfl (hx.trans hxy)) (hint le_rfl hx)
  rw [hdiff]
  refine ⟨intervalIntegral.integral_nonneg hxy (fun t ht => (hf t (hx.trans ht.1)).1), ?_⟩
  have hupper : (∫ t in x..y, f t / Real.log t) ≤ ∫ _ in x..y, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hxy (hint hx hxy) intervalIntegrable_const
      (fun t ht => (hf t (hx.trans ht.1)).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hupper

private theorem coefficient_eq_zero (G : ℝ → ℝ) {n : ℕ} (hn : n ≤ 8) : coefficient G n = 0 := by
  rw [coefficient, if_neg (by omega)]

private theorem coefficient_binary {G : ℝ → ℝ}
    (hG : ∀ ⦃s t : ℝ⦄, 8 ≤ s → s ≤ t → 0 ≤ G t - G s ∧ G t - G s ≤ t - s)
    (n : ℕ) : coefficient G n = 0 ∨ coefficient G n = 1 := by
  by_cases hn : 9 ≤ n
  · have hprev : (8 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (8 : ℕ) ≤ n - 1 by omega)
    have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
    have hstep : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show n = (n - 1) + 1 by omega)
    obtain ⟨hlower, hupper⟩ := hG hprev hle
    have hlo : ⌊G ((n - 1 : ℕ) : ℝ)⌋ ≤ ⌊G (n : ℝ)⌋ :=
      Int.floor_mono (sub_nonneg.mp hlower)
    have hhi : ⌊G (n : ℝ)⌋ ≤ ⌊G ((n - 1 : ℕ) : ℝ)⌋ + 1 := by
      have h : G (n : ℝ) ≤ G ((n - 1 : ℕ) : ℝ) + 1 :=
        by linarith only [hupper, hstep]
      simpa only [Int.floor_add_one] using Int.floor_mono h
    have hd : (⌊G (n : ℝ)⌋ - ⌊G ((n - 1 : ℕ) : ℝ)⌋ : ℤ) = 0 ∨
        (⌊G (n : ℝ)⌋ - ⌊G ((n - 1 : ℕ) : ℝ)⌋ : ℤ) = 1 := by omega
    rcases hd with hd | hd
    · left
      simp only [coefficient, if_pos hn, hd, Int.cast_zero]
    · right
      simp only [coefficient, if_pos hn, hd, Int.cast_one]
  · exact Or.inl (coefficient_eq_zero G (by omega))

private theorem sum_coefficient {G : ℝ → ℝ} (hG8 : G 8 = 0) (m : ℕ) (hm : 8 ≤ m) :
    (∑ n ∈ Finset.Icc 0 m, coefficient G n) = (⌊G (m : ℝ)⌋ : ℝ) := by
  refine Nat.le_induction ?_ ?_ m hm
  · have hz : (∑ n ∈ Finset.Icc 0 8, coefficient G n) = 0 :=
      Finset.sum_eq_zero (fun n hn => coefficient_eq_zero G (Finset.mem_Icc.mp hn).2)
    simpa [hG8] using hz
  · intro k hk ih
    have hnext : 9 ≤ k + 1 := by omega
    rw [Finset.sum_Icc_succ_top (Nat.zero_le (k + 1)), ih, coefficient, if_pos hnext,
      show k + 1 - 1 = k by omega, Int.cast_sub]
    ring

private theorem abs_prefix_error {G : ℝ → ℝ} (hG8 : G 8 = 0)
    (hG : ∀ ⦃s t : ℝ⦄, 8 ≤ s → s ≤ t → 0 ≤ G t - G s ∧ G t - G s ≤ t - s)
    (x : ℝ) (hx : 8 ≤ x) : |prefixCount (coefficient G) x - G x| ≤ 2 := by
  have hm : 8 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hm8 : (8 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hm
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith only [hx])
  have hcut : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  obtain ⟨hlower, hupper⟩ := hG hm8 hmx
  have hfloor := Int.floor_le (G (⌊x⌋₊ : ℝ))
  have hfloor' := Int.lt_floor_add_one (G (⌊x⌋₊ : ℝ))
  rw [prefixCount, sum_coefficient hG8 _ hm]
  exact abs_le.mpr ⟨by linarith only [hupper, hfloor', hcut], by linarith only [hlower, hfloor]⟩

private theorem logCount_abel (c : ℕ → ℝ) (hc : ∀ n ≤ 8, c n = 0)
    {x : ℝ} (hx : 8 ≤ x)
    (hd : ∀ t ∈ Set.Icc (8 : ℝ) x, HasDerivAt Real.log t⁻¹ t)
    (hi : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc 8 x)) :
    logCount c x = Real.log x * prefixCount c x -
      ∫ t in (8 : ℝ)..x, t⁻¹ * prefixCount c t := by
  have hfloor8 : ⌊(8 : ℝ)⌋₊ = 8 := by simp
  have hzero : (∑ n ∈ Finset.Icc 0 8, c n) = 0 := by
    exact Finset.sum_eq_zero (fun n hn => hc n (Finset.mem_Icc.mp hn).2)
  have hsum :
      (∑ n ∈ Finset.Ioc 8 ⌊x⌋₊, Real.log (n : ℝ) * c n) = logCount c x := by
    unfold logCount
    apply Finset.sum_subset
    · intro n hn
      have hnx := (Finset.mem_Ioc.mp hn).2
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnx⟩
    · intro n hn hn'
      have hnx := (Finset.mem_Icc.mp hn).2
      have hn8 : n ≤ 8 :=
        le_of_not_gt (fun h => hn' (Finset.mem_Ioc.mpr ⟨h, hnx⟩))
      simp only [hc n hn8, mul_zero]
  have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := Real.log)
    (by norm_num : (0 : ℝ) ≤ 8) hx (fun t ht => (hd t ht).differentiableAt)
    (by simpa only [Real.deriv_log'] using hi)
  rw [← hsum]
  simpa only [hfloor8, hzero, mul_zero, sub_zero, Real.deriv_log,
    ← intervalIntegral.integral_of_le hx, prefixCount] using habel

private theorem logCount_coefficient_error {F f : ℝ → ℝ}
    (hF : ∀ t : ℝ, 8 ≤ t → HasDerivAt F (f t) t)
    (hf : ContinuousOn f (Set.Ici (8 : ℝ)))
    (hρ : ContinuousOn (fun t => f t / Real.log t) (Set.Ici (8 : ℝ)))
    (hclose : ∀ t : ℝ, 8 ≤ t →
      |prefixCount (coefficient (primitive f)) t - primitive f t| ≤ 2)
    (x : ℝ) (hx : 8 ≤ x) :
    |logCount (coefficient (primitive f)) x - F x| ≤ |F 8| + 4 * Real.log x := by
  let G := primitive f
  let c := coefficient G
  change |logCount c x - F x| ≤ |F 8| + 4 * Real.log x
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (8 : ℝ) x) : 0 < t :=
    (by norm_num : (0 : ℝ) < 8).trans_le ht.1
  have hlogDeriv (t : ℝ) (ht : t ∈ Set.Icc (8 : ℝ) x) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (hpos t ht).ne'
  have hlogCont : ContinuousOn Real.log (Set.Icc (8 : ℝ) x) :=
    fun t ht => (hlogDeriv t ht).continuousAt.continuousWithinAt
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 8 x) :=
    continuousOn_id.inv₀ (fun t ht => (hpos t ht).ne')
  have hinvInt : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 8 x :=
    hinv.intervalIntegrable_of_Icc hx
  have hρInt : IntervalIntegrable (fun t => f t / Real.log t) volume 8 x :=
    (hρ.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hx
  have hGCont : ContinuousOn G (Set.uIcc (8 : ℝ) x) :=
    intervalIntegral.continuousOn_primitive_interval' hρInt Set.left_mem_uIcc
  have hρOpen : ContinuousOn (fun t => f t / Real.log t) (Set.Ioi (8 : ℝ)) :=
    hρ.mono Set.Ioi_subset_Ici_self
  have hGDeriv (t : ℝ) (ht : 8 < t) : HasDerivAt G (f t / Real.log t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hρ.mono (fun _ hu => hu.1)).intervalIntegrable_of_Icc ht.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hρOpen t ht)
      (hρOpen.continuousAt (isOpen_Ioi.mem_nhds ht))
  have hFInt : (∫ t in (8 : ℝ)..x, f t) = F x - F 8 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hF t (show t ∈ Set.Icc (8 : ℝ) x from Set.uIcc_of_le hx ▸ ht).1)
      ((hf.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hx)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := Real.log) (u' := fun t : ℝ => t⁻¹) (v := G) (v' := fun t => f t / Real.log t)
    ((Set.uIcc_of_le hx).symm ▸ hlogCont) hGCont
    (fun t ht => hlogDeriv t
      (Set.Ioo_subset_Icc_self (by simpa only [min_eq_left hx, max_eq_right hx] using ht)))
    (fun t ht => hGDeriv t (by simpa only [min_eq_left hx] using ht.1))
    hinvInt hρInt
  have hw : (∫ t in (8 : ℝ)..x, Real.log t * (f t / Real.log t)) =
      ∫ t in (8 : ℝ)..x, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (8 : ℝ) x := Set.uIcc_of_le hx ▸ ht
    change Real.log t * (f t / Real.log t) = f t
    rw [mul_comm (Real.log t), div_mul_cancel₀ _ (log_pos_of_eight_le ht'.1).ne']
  have hG8 : G 8 = 0 := primitive_at_eight f
  rw [hw, hFInt, hG8, mul_zero, sub_zero] at hparts
  have habel := logCount_abel c (fun _ hn => coefficient_eq_zero G hn) hx
    hlogDeriv hinv.integrableOn_Icc
  have hPInt : IntervalIntegrable (fun t => t⁻¹ * prefixCount c t) volume 8 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2
      (integrableOn_mul_sum_Icc c (by norm_num : (0 : ℝ) ≤ 8) hinv.integrableOn_Icc)
  have hGInt : IntervalIntegrable (fun t => t⁻¹ * G t) volume 8 x :=
    hinvInt.mul_continuousOn hGCont
  have herrInt : IntervalIntegrable (fun t => t⁻¹ * (prefixCount c t - G t)) volume 8 x := by
    simpa only [mul_sub] using hPInt.sub hGInt
  have hcenter : logCount c x - (F x - F 8) =
      Real.log x * (prefixCount c x - G x) -
        ∫ t in (8 : ℝ)..x, t⁻¹ * (prefixCount c t - G t) := by
    rw [habel, hparts]
    simp only [mul_sub, intervalIntegral.integral_sub hPInt hGInt]
    ring
  have hboundary : |Real.log x * (prefixCount c x - G x)| ≤ 2 * Real.log x := by
    have hlogx := (log_pos_of_eight_le hx).le
    rw [abs_mul, abs_of_nonneg hlogx, mul_comm (2 : ℝ) (Real.log x)]
    exact mul_le_mul_of_nonneg_left (hclose x hx) hlogx
  have hinvFTC : (∫ t in (8 : ℝ)..x, t⁻¹) = Real.log x - Real.log 8 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hlogDeriv t (Set.uIcc_of_le hx ▸ ht)) hinvInt
  have hintegral : |∫ t in (8 : ℝ)..x, t⁻¹ * (prefixCount c t - G t)| ≤ 2 * Real.log x := by
    calc
      _ ≤ ∫ t in (8 : ℝ)..x, |t⁻¹ * (prefixCount c t - G t)| :=
        intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in (8 : ℝ)..x, 2 * t⁻¹ := by
        refine intervalIntegral.integral_mono_on hx herrInt.abs (hinvInt.const_mul 2) ?_
        intro t ht
        have ht0 := inv_nonneg.mpr (hpos t ht).le
        rw [abs_mul, abs_of_nonneg ht0, mul_comm (2 : ℝ) (t⁻¹)]
        exact mul_le_mul_of_nonneg_left (hclose t ht.1) ht0
      _ = 2 * (Real.log x - Real.log 8) := by
        rw [intervalIntegral.integral_const_mul, hinvFTC]
      _ ≤ _ := by linarith only [log_pos_of_eight_le (le_rfl : (8 : ℝ) ≤ 8)]
  have hcenterBound : |logCount c x - (F x - F 8)| ≤ 4 * Real.log x := by
    rw [hcenter]
    exact (abs_sub _ _).trans (by linarith only [hboundary, hintegral])
  calc
    |logCount c x - F x| = |(logCount c x - (F x - F 8)) - F 8| := by
      congr 1
      ring
    _ ≤ |logCount c x - (F x - F 8)| + |F 8| := abs_sub _ _
    _ ≤ |F 8| + 4 * Real.log x := by linarith only [hcenterBound]

/-- Rounding the primitive gives binary coefficients and a uniform logarithmic error at
every real cutoff at least eight. -/
private theorem exists_binary_log_count {F f : ℝ → ℝ}
    (hF : ∀ t : ℝ, 8 ≤ t → HasDerivAt F (f t) t)
    (hf : ContinuousOn f (Set.Ici (8 : ℝ)))
    (hρ : ∀ t : ℝ, 8 ≤ t → 0 ≤ f t / Real.log t ∧ f t / Real.log t ≤ 1) :
    ∃ c : ℕ → ℝ, (∀ n, c n = 0 ∨ c n = 1) ∧
      (∀ n ≤ 8, c n = 0) ∧
      ∀ x : ℝ, 8 ≤ x → |logCount c x - F x| ≤ |F 8| + 4 * Real.log x := by
  have hcont := density_continuousOn hf
  have hstep ⦃s t : ℝ⦄ (hs : 8 ≤ s) (hst : s ≤ t) :
      0 ≤ primitive f t - primitive f s ∧ primitive f t - primitive f s ≤ t - s :=
    primitive_increment hcont hρ hs hst
  refine ⟨coefficient (primitive f), coefficient_binary hstep,
    fun _ hn => coefficient_eq_zero _ hn, ?_⟩
  exact logCount_coefficient_error hF hf hcont (abs_prefix_error (primitive_at_eight f) hstep)

/-! ## The rounded tail and its window estimates -/

/-- The integrand of the actual tail of the finite log-weighted count. -/
def roundedTailKernel (c : ℕ → ℝ) (x : ℝ) : ℝ := (logCount c x - x) / x ^ 2

private def roundedTail (c : ℕ → ℝ) (x : ℝ) : ℝ := ∫ t in Ioi x, roundedTailKernel c t

def roundedSignedMass (c : ℕ → ℝ) (A B : ℝ) : ℝ :=
  ∫ x in A..B, roundedTail c x / Real.sqrt x

def roundedNegativeMass (c : ℕ → ℝ) (A B : ℝ) : ℝ :=
  ∫ x in A..B, max (-roundedTail c x) 0 / Real.sqrt x

private lemma one_le_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 1 ≤ x :=
  (by norm_num : (1 : ℝ) ≤ 8).trans hx

private lemma pos_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 0 < x :=
  zero_lt_one.trans_le (one_le_of_eight_le hx)

private lemma continuousOn_countSlope : ContinuousOn countSlope (Ici (8 : ℝ)) := by
  have hpow (p : ℝ) : ContinuousOn (fun x : ℝ => x ^ p) (Ici (8 : ℝ)) :=
    fun x hx => (Real.continuousAt_rpow_const x p
      (Or.inl (pos_of_eight_le hx).ne')).continuousWithinAt
  have hu : ContinuousOn phase (Ici (8 : ℝ)) := hpow (1 / 6)
  have hs := Real.continuous_sin.comp_continuousOn' hu
  have hc := Real.continuous_cos.comp_continuousOn' hu
  unfold countSlope
  exact (((continuousOn_const.sub (continuousOn_const.mul (hpow (-1 / 2)))).add
    ((continuousOn_const.mul (hpow (-1 / 3))).mul hs)).sub
    ((continuousOn_const.mul (hpow (-1 / 6))).mul hc)).add (continuousOn_const.mul hs)

private lemma density_bounds (x : ℝ) (hx : 8 ≤ x) :
    0 ≤ countSlope x / Real.log x ∧ countSlope x / Real.log x ≤ 1 := by
  have hlog8 : (4 / 3 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
    linarith only [Real.log_two_gt_d9]
  have hlog := hlog8.trans (Real.log_le_log (by norm_num) hx)
  have hlogpos : 0 < Real.log x := by linarith only [hlog]
  obtain ⟨hslo, hshi⟩ := countSlope_bounds (one_le_of_eight_le hx)
  exact ⟨div_nonneg (by linarith only [hslo]) hlogpos.le, (div_le_one hlogpos).2 (hshi.trans hlog)⟩

private lemma logCount_jump (c : ℕ → ℝ) (n : ℕ) :
    logCount c ((n + 1 : ℕ) : ℝ) - logCount c (n : ℝ) =
      Real.log ((n + 1 : ℕ) : ℝ) * c (n + 1) := by
  simp only [logCount, Nat.floor_natCast]
  rw [Finset.sum_Icc_succ_top (Nat.zero_le (n + 1))]
  ring

private lemma measurable_logCount (c : ℕ → ℝ) : Measurable (logCount c) := by
  let partialSum (m : ℕ) : ℝ := ∑ n ∈ Finset.Icc 0 m, Real.log (n : ℝ) * c n
  exact (measurable_of_countable partialSum).comp Nat.measurable_floor

private def countErrorConstant : ℝ := |count 8| + 16

private lemma countErrorConstant_nonneg : 0 ≤ countErrorConstant := by
  unfold countErrorConstant
  linarith only [abs_nonneg (count 8)]

private lemma log_le_four_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / 4 : ℝ))
  rw [Real.log_rpow hx] at h
  linarith only [h]

section RoundingError

variable {c : ℕ → ℝ}
variable (hround : ∀ x : ℝ, 8 ≤ x → |logCount c x - count x| ≤ |count 8| + 4 * Real.log x)

include hround in
private lemma rounded_count_error {x : ℝ} (hx : 8 ≤ x) :
    |logCount c x - count x| ≤ countErrorConstant * x ^ (1 / 4 : ℝ) := by
  have hpow : 1 ≤ x ^ (1 / 4 : ℝ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (one_le_of_eight_le hx) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hconst : |count 8| ≤ |count 8| * x ^ (1 / 4 : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (abs_nonneg (count 8))
  apply (hround x hx).trans
  unfold countErrorConstant
  rw [add_mul]
  linarith only [hconst, log_le_four_rpow (pos_of_eight_le hx)]

include hround in
private lemma rounded_count_pnt : Tendsto (fun x : ℝ => logCount c x / x) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (g := fun x : ℝ => (countErrorConstant + 3 / 2) * x ^ (-1 / 6 : ℝ))
    (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (8 : ℝ)] with x hx
    have hx₀ := pos_of_eight_le hx
    have hratio : logCount c x / x - 1 = (logCount c x - x) / x := by
      rw [sub_div, div_self hx₀.ne']
    have hpow : x ^ (5 / 6 : ℝ) / x = x ^ (-1 / 6 : ℝ) := by
      rw [← Real.rpow_sub_one hx₀.ne', show (5 / 6 : ℝ) - 1 = -1 / 6 by norm_num]
    have hquarter : x ^ (1 / 4 : ℝ) ≤ x ^ (5 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_of_eight_le hx) (by norm_num)
    have hcount : |logCount c x - x| ≤ (countErrorConstant + 3 / 2) * x ^ (5 / 6 : ℝ) := by
      calc
        _ = |(logCount c x - count x) + (count x - x)| := by congr 1 <;> ring
        _ ≤ |logCount c x - count x| + |count x - x| := abs_add_le _ _
        _ ≤ _ := by
          rw [add_mul]
          exact add_le_add ((rounded_count_error hround hx).trans
            (mul_le_mul_of_nonneg_left hquarter countErrorConstant_nonneg))
            (count_error (one_le_of_eight_le hx))
    rw [Real.norm_eq_abs, hratio, abs_div, abs_of_pos hx₀]
    calc
      _ ≤ ((countErrorConstant + 3 / 2) * x ^ (5 / 6 : ℝ)) / x :=
        div_le_div_of_nonneg_right hcount hx₀.le
      _ = _ := by rw [mul_div_assoc, hpow]
  · have h : Tendsto (fun x : ℝ => x ^ (-1 / 6 : ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div] using
        (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 6 : ℝ)))
    simpa only [mul_zero] using h.const_mul (countErrorConstant + 3 / 2)

private def errorKernel (c : ℕ → ℝ) (t : ℝ) : ℝ := (logCount c t - count t) / t ^ 2

private lemma tailKernel_sub (c : ℕ → ℝ) (t : ℝ) :
    roundedTailKernel c t - tailKernel t = errorKernel c t := by
  unfold roundedTailKernel tailKernel errorKernel
  rw [← sub_div]
  congr 1 <;> ring

include hround in
private lemma abs_errorKernel_le {t : ℝ} (ht : 8 ≤ t) :
    |errorKernel c t| ≤ countErrorConstant * t ^ (-7 / 4 : ℝ) := by
  rw [errorKernel, abs_div, abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ (countErrorConstant * t ^ (1 / 4 : ℝ)) / t ^ 2 :=
      div_le_div_of_nonneg_right (rounded_count_error hround ht) (sq_nonneg t)
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_two t, ← Real.rpow_sub (pos_of_eight_le ht),
        show (1 / 4 : ℝ) - 2 = -7 / 4 by norm_num]

include hround in
private lemma integrableOn_errorKernel {x : ℝ} (hx : 8 ≤ x) :
    IntegrableOn (errorKernel c) (Ioi x) := by
  have hcount : ContinuousOn count (Ioi x) := fun t ht =>
    (hasDerivAt_count ((pos_of_eight_le hx).trans (mem_Ioi.mp ht))).continuousAt.continuousWithinAt
  have hsq : Measurable (fun t : ℝ => t ^ (2 : ℕ)) := measurable_id.pow_const 2
  have hmeas : AEStronglyMeasurable (errorKernel c) (volume.restrict (Ioi x)) :=
    ((measurable_logCount c).aestronglyMeasurable.sub
      (hcount.aestronglyMeasurable measurableSet_Ioi)).div₀ hsq.aestronglyMeasurable
  refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-7 / 4 : ℝ) < -1)
    (pos_of_eight_le hx)).const_mul countErrorConstant).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi x) measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using abs_errorKernel_le hround (hx.trans (mem_Ioi.mp ht).le)

include hround in
private lemma integrableOn_roundedTailKernel {x : ℝ} (hx : 8 ≤ x) :
    IntegrableOn (roundedTailKernel c) (Ioi x) := by
  refine ((integrableOn_tailKernel (one_le_of_eight_le hx)).add
    (integrableOn_errorKernel hround hx)).congr_fun ?_ measurableSet_Ioi
  intro t _
  change tailKernel t + errorKernel c t = roundedTailKernel c t
  rw [← tailKernel_sub]
  ring

include hround in
private lemma roundedTail_error {x : ℝ} (hx : 8 ≤ x) :
    |roundedTail c x - integratedTail x| ≤ (4 / 3 : ℝ) * countErrorConstant * x ^ (-3 / 4 : ℝ) := by
  have hdiff : roundedTail c x - integratedTail x = ∫ t in Ioi x, errorKernel c t := by
    unfold roundedTail integratedTail
    rw [← MeasureTheory.integral_sub (integrableOn_roundedTailKernel hround hx)
      (integrableOn_tailKernel (one_le_of_eight_le hx))]
    exact integral_congr_ae (Eventually.of_forall (tailKernel_sub c))
  rw [hdiff]
  calc
    _ ≤ ∫ t in Ioi x, countErrorConstant * t ^ (-7 / 4 : ℝ) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-7 / 4 : ℝ) < -1)
          (pos_of_eight_le hx)).const_mul countErrorConstant)
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi x) measurableSet_Ioi] with t ht
      simpa only [Real.norm_eq_abs] using abs_errorKernel_le hround (hx.trans (mem_Ioi.mp ht).le)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : (-7 / 4 : ℝ) < -1) (pos_of_eight_le hx),
        show (-7 / 4 : ℝ) + 1 = -3 / 4 by norm_num]
      ring

private def windowMajorant (x : ℝ) : ℝ := (4 / 3 : ℝ) * countErrorConstant * x ^ (-5 / 4 : ℝ)

private lemma windowMajorant_nonneg {x : ℝ} (hx : 8 ≤ x) : 0 ≤ windowMajorant x :=
  mul_nonneg (mul_nonneg (by norm_num) countErrorConstant_nonneg)
    (Real.rpow_nonneg (pos_of_eight_le hx).le _)

private lemma windowMajorant_integrable : IntegrableOn windowMajorant (Ioi (8 : ℝ)) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) (by norm_num : (0 : ℝ) < 8)).const_mul
    ((4 / 3 : ℝ) * countErrorConstant)

private def windowError : ℝ := ∫ t in Ioi (8 : ℝ), windowMajorant t

private lemma windowError_nonneg : 0 ≤ windowError :=
  setIntegral_nonneg measurableSet_Ioi (fun _ ht => windowMajorant_nonneg (mem_Ioi.mp ht).le)

include hround in
private lemma weighted_tail_error {x : ℝ} (hx : 8 ≤ x) :
    |roundedTail c x - integratedTail x| / Real.sqrt x ≤ windowMajorant x := by
  calc
    _ ≤ ((4 / 3 : ℝ) * countErrorConstant * x ^ (-3 / 4 : ℝ)) / Real.sqrt x :=
      div_le_div_of_nonneg_right (roundedTail_error hround hx) (Real.sqrt_nonneg x)
    _ = _ := by
      rw [windowMajorant, mul_div_assoc, Real.sqrt_eq_rpow, ← Real.rpow_sub (pos_of_eight_le hx),
        show (-3 / 4 : ℝ) - 1 / 2 = -5 / 4 by norm_num]

private lemma continuousOn_tail {k : ℝ → ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hk : IntegrableOn k (Ioi A)) : ContinuousOn (fun x => ∫ t in Ioi x, k t) (uIcc A B) := by
  have hi : IntervalIntegrable k volume A B :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).2 (hk.mono_set Ioc_subset_Ioi_self)
  have hcont : ContinuousOn (fun x => (∫ t in Ioi A, k t) - ∫ t in A..x, k t) (uIcc A B) :=
    continuousOn_const.sub (intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc)
  apply hcont.congr
  intro x hx
  have hx' : x ∈ Icc A B := uIcc_of_le hAB ▸ hx
  change (∫ t in Ioi x, k t) = (∫ t in Ioi A, k t) - ∫ t in A..x, k t
  linarith only [intervalIntegral.integral_Ioi_sub_Ioi hk (mem_Icc.mp hx').1]

include hround in
private lemma window_discrepancy {A B : ℝ} (hA : 8 ≤ A) (hAB : A ≤ B)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφbound : ∀ u v, |φ u - φ v| ≤ |u - v|) :
    |(∫ x in A..B, φ (roundedTail c x) / Real.sqrt x) -
      (∫ x in A..B, φ (integratedTail x) / Real.sqrt x)| ≤ windowError := by
  have hsqrt (x : ℝ) (hx : x ∈ uIcc A B) : Real.sqrt x ≠ 0 := by
    have hx' : x ∈ Icc A B := uIcc_of_le hAB ▸ hx
    exact (Real.sqrt_pos.2 (pos_of_eight_le (hA.trans (mem_Icc.mp hx').1))).ne'
  have hroundCont : ContinuousOn (roundedTail c) (uIcc A B) :=
    continuousOn_tail hAB (integrableOn_roundedTailKernel hround hA)
  have hmodelCont : ContinuousOn integratedTail (uIcc A B) :=
    continuousOn_tail hAB (integrableOn_tailKernel (one_le_of_eight_le hA))
  have hi {q : ℝ → ℝ} (hq : ContinuousOn q (uIcc A B)) :
      IntervalIntegrable (fun x => φ (q x) / Real.sqrt x) volume A B :=
    ((hφ.comp_continuousOn' hq).div Real.continuous_sqrt.continuousOn hsqrt).intervalIntegrable
  have hsub : Ioc A B ⊆ Ioi (8 : ℝ) := fun _ hx => hA.trans_lt (mem_Ioc.mp hx).1
  rw [← intervalIntegral.integral_sub (hi hroundCont) (hi hmodelCont), intervalIntegral.integral_of_le hAB]
  calc
    _ ≤ ∫ x in Ioc A B, windowMajorant x := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (windowMajorant_integrable.mono_set hsub)
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc A B) measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
      exact (div_le_div_of_nonneg_right (hφbound _ _) (Real.sqrt_nonneg x)).trans
        (weighted_tail_error hround (mem_Ioi.mp (hsub hx)).le)
    _ ≤ windowError := by
      refine setIntegral_mono_set windowMajorant_integrable ?_ hsub.eventuallySubset
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (8 : ℝ)) measurableSet_Ioi] with x hx
      exact windowMajorant_nonneg (mem_Ioi.mp hx).le

include hround in
private lemma window_mass_errors {A B : ℝ} (hA : 8 ≤ A) (hAB : A ≤ B) :
    |roundedSignedMass c A B - signedMass A B| ≤ windowError ∧
      |roundedNegativeMass c A B - negativeMass A B| ≤ windowError := by
  have hneg : Continuous (fun u : ℝ => max (-u) 0) := continuous_id.neg.sup continuous_const
  refine ⟨window_discrepancy hround hA hAB continuous_id (fun _ _ => le_rfl),
    window_discrepancy hround hA hAB hneg ?_⟩
  intro u v
  calc
    _ ≤ |(-u) - (-v)| := abs_max_sub_max_le_abs _ _ _
    _ = |u - v| := by rw [neg_sub_neg, abs_sub_comm]

include hround in
private lemma roundedNegativeMass_power_window {b : ℝ} (hb : 1 < b) :
    ∀ᶠ Y : ℝ in atTop, (1 / 4 : ℝ) * Y ^ (b / 6) ≤ roundedNegativeMass c Y (Y ^ b) := by
  have hlarge : ∀ᶠ Y : ℝ in atTop, 4 * windowError ≤ Y ^ (b / 6) :=
    (tendsto_rpow_atTop (by linarith only [hb] : 0 < b / 6)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (8 : ℝ), negativeMass_power_window hb, hlarge] with Y hY hbase hlargeY
  have hwindow : Y ≤ Y ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (one_le_of_eight_le hY) hb.le
  have hdiff := (abs_le.mp (window_mass_errors hround hY hwindow).2).1
  linarith only [hbase, hlargeY, hdiff]

end RoundingError

/-- A binary log-weighted integer count with its actual tail and simultaneous window bounds. -/
theorem roundedWindowObstruction :
    ∃ (c : ℕ → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, c n = 0 ∨ c n = 1) ∧
      (∀ n ≤ 8, c n = 0) ∧
      (∀ n : ℕ, logCount c ((n + 1 : ℕ) : ℝ) - logCount c (n : ℝ) =
        Real.log ((n + 1 : ℕ) : ℝ) * c (n + 1)) ∧
      (∀ x : ℝ, 8 ≤ x → |logCount c x - count x| ≤ |count 8| + 4 * Real.log x ∧
        IntegrableOn (roundedTailKernel c) (Ioi x)) ∧
      Tendsto (fun x : ℝ => logCount c x / x) atTop (𝓝 1) ∧
      (∀ A B : ℝ, 8 ≤ A → A ≤ B →
        |roundedSignedMass c A B + 2 * Real.log (B / A)| ≤ C ∧
        (3 / 2 : ℝ) * (B ^ (1 / 6 : ℝ) - A ^ (1 / 6 : ℝ)) - C ≤ roundedNegativeMass c A B) ∧
      (∀ b : ℝ, 1 < b → ∀ᶠ Y : ℝ in atTop,
        (1 / 4 : ℝ) * Y ^ (b / 6) ≤ roundedNegativeMass c Y (Y ^ b)) := by
  obtain ⟨c, hc, hzero, hround⟩ := exists_binary_log_count (F := count) (f := countSlope)
    (fun _ ht => hasDerivAt_count (pos_of_eight_le ht)) continuousOn_countSlope density_bounds
  obtain ⟨_, _, _, _, hcontinuumWindow, _⟩ := continuumCountermodel
  refine ⟨c, windowError + 12, by linarith only [windowError_nonneg], hc, hzero, logCount_jump c,
    fun x hx => ⟨hround x hx, integrableOn_roundedTailKernel hround hx⟩,
    rounded_count_pnt hround, ?_, fun _ hb => roundedNegativeMass_power_window hround hb⟩
  intro A B hA hAB
  obtain ⟨hs, hn⟩ := window_mass_errors hround hA hAB
  constructor
  · have hmodel := (hcontinuumWindow A B (one_le_of_eight_le hA) hAB).1
    calc
      _ = |(roundedSignedMass c A B - signedMass A B) + (signedMass A B + 2 * Real.log (B / A))| := by
        congr 1 <;> ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hs hmodel)
  · have hmodel := (hcontinuumWindow A B (one_le_of_eight_le hA) hAB).2
    change (3 / 2 : ℝ) * (B ^ (1 / 6 : ℝ) - A ^ (1 / 6 : ℝ)) - 15 / 2 ≤ negativeMass A B at hmodel
    linarith only [hmodel, (abs_le.mp hn).1]

end D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel
