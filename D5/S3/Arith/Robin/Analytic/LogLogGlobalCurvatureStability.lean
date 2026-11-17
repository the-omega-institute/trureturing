/- GID: D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvatureStability
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LogLogGlobalCurvatureStability
   mirror-E: none(waiver:global-real-analysis)
   anchors: []
   utility: none
   digest: Global and half-scale stability bounds for the log-log tangent gap. -/

/- The estimate is scalar and global: the clock mismatch may be the complete
   higher mismatch, with no small-displacement assumption. This file contains
   no record/prime wrapper or claim of a Robin/RH realization. -/

import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.MellinWeightedVariation
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability

open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity g_has_deriv_at)
open D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature (loglog_tangent_gap_quadratic)
open D5.S3.Arith.Robin.ArithmeticMixedCornerResponse (density_antitone)

private theorem density_nonneg {t : ℝ} (ht : 1 < t) :
    0 ≤ activationDensity t := by
  exact D5.S3.Arith.Robin.MellinWeightedVariation.weight_nonneg ht

/- The actual derivative -w is bounded on the WHOLE interval between the
endpoints. Mathlib's mean-value inequality includes coincident endpoints and
both orders; this is not a bound restricted to a displacement neighbourhood. -/
private theorem g_sub_le {c a y : ℝ} (hc : 1 < c) (hca : c ≤ a) (hcy : c ≤ y) :
    |g a - g y| ≤ activationDensity c * |a - y| := by
  have hdom (t : ℝ) (ht : t ∈ Icc (min a y) (max a y)) : c ≤ t :=
    (le_min hca hcy).trans ht.1
  have hd (t : ℝ) (ht : t ∈ Icc (min a y) (max a y)) :
      HasDerivWithinAt g (-activationDensity t) (Icc (min a y) (max a y)) t :=
    (g_has_deriv_at (hc.trans_le (hdom t ht))).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Icc (min a y) (max a y)) :
      ‖-activationDensity t‖ ≤ activationDensity c := by
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (density_nonneg (hc.trans_le (hdom t ht)))]
    exact density_antitone hc (hdom t ht)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc (min a y) (max a y))
    (show y ∈ Icc (min a y) (max a y) from
      ⟨min_le_right a y, le_max_right a y⟩)
    (show a ∈ Icc (min a y) (max a y) from
      ⟨min_le_left a y, le_max_left a y⟩)
  simpa only [Real.norm_eq_abs] using hm

/-- Global three-clock stability of the log-log tangent gap. All three clocks
are arbitrary real numbers greater than one, in any order, including equality.
The quantities M and d are complete absolute differences, not truncated ones. -/
theorem loglog_tangent_gap_stability {a x y : ℝ}
    (ha : 1 < a) (hx : 1 < x) (hy : 1 < y) :
    let K := fun z : ℝ => Real.log (Real.log a) + (z - a) / (a * Real.log a) -
      Real.log (Real.log z)
    let w := fun t : ℝ => (1 + Real.log t) / (t ^ 2 * (Real.log t) ^ 2)
    let c := min a (min x y)
    let M := |x - y|
    let d := |y - a|
    |K x - K y| ≤ w c * (d * M + M ^ 2 / 2) := by
  dsimp only
  let c := min a (min x y)
  let M := |x - y|
  let d := |y - a|
  let K : ℝ → ℝ → ℝ := fun s t =>
    Real.log (Real.log s) + (t - s) / (s * Real.log s) - Real.log (Real.log t)
  have hc : 1 < c := lt_min ha (lt_min hx hy)
  have hca : c ≤ a := min_le_left a (min x y)
  have hcx : c ≤ x := (min_le_right a (min x y)).trans (min_le_left x y)
  have hcy : c ≤ y := (min_le_right a (min x y)).trans (min_le_right x y)
  have hcm : c ≤ min y x := le_min hcy hcx

  have hg : |g a - g y| ≤ activationDensity c * d := by
    have h := g_sub_le hc hca hcy
    rw [abs_sub_comm a y] at h
    exact h
  have hquad :
      activationDensity (max y x) * (x - y) ^ 2 / 2 ≤ K y x ∧
      K y x ≤ activationDensity (min y x) * (x - y) ^ 2 / 2 := by
    simpa only [K, activationDensity, add_comm] using
      (loglog_tangent_gap_quadratic hy hx)
  have hK0 : 0 ≤ K y x :=
    (show 0 ≤ activationDensity (max y x) * (x - y) ^ 2 / 2 by
      exact div_nonneg (mul_nonneg
        (density_nonneg (hy.trans_le (le_max_left y x))) (sq_nonneg _))
        (by norm_num)).trans hquad.1
  have hK : |K y x| ≤ activationDensity c * M ^ 2 / 2 := by
    rw [abs_of_nonneg hK0]
    calc
      K y x ≤ activationDensity (min y x) * (x - y) ^ 2 / 2 := hquad.2
      _ ≤ activationDensity c * (x - y) ^ 2 / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (density_antitone hc hcm) (sq_nonneg _))
          (by norm_num)
      _ = activationDensity c * M ^ 2 / 2 := by simp only [M, sq_abs]

  have hcocycle : K a x - K a y = (g a - g y) * (x - y) + K y x := by
    simp only [K, g, div_eq_mul_inv]
    ring
  have hlinear : |(g a - g y) * (x - y)| ≤ activationDensity c * d * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hg (abs_nonneg (x - y))
  have hfinal : |K a x - K a y| ≤ activationDensity c * (d * M + M ^ 2 / 2) := by
    calc
      |K a x - K a y| = |(g a - g y) * (x - y) + K y x| :=
        congrArg abs hcocycle
      _ ≤ |(g a - g y) * (x - y)| + |K y x| := abs_add_le _ _
      _ ≤ activationDensity c * d * M + activationDensity c * M ^ 2 / 2 :=
        add_le_add hlinear hK
      _ = activationDensity c * (d * M + M ^ 2 / 2) := by ring
  simpa only [K, c, M, d, activationDensity, add_comm] using hfinal

/- The half-scale coefficient, with every logarithmic/denominator sign exposed.
This uses log 2 ≤ 1, log a ≥ 2, hence L/2 ≤ H and H ≥ 1. The polynomial
inequality (1+H)L ≤ 4H² then supplies the factor 16 after scaling by (a/2)². -/
private theorem density_half_le {a : ℝ} (ha : Real.exp 2 ≤ a) :
    1 < a / 2 ∧ activationDensity (a / 2) ≤ 16 / (a ^ 2 * Real.log a) := by
  have ha3 : 3 ≤ a := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hhalf : 1 < a / 2 := by linarith
  have hL : 2 ≤ Real.log a := (Real.le_log_iff_exp_le ha0).mpr ha
  have hL0 : 0 < Real.log a := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1 <;> norm_num
  have hHlower : Real.log a / 2 ≤ Real.log (a / 2) := by
    rw [Real.log_div ha0.ne' (show (2 : ℝ) ≠ 0 by norm_num)]
    linarith
  have hH : 1 ≤ Real.log (a / 2) := by linarith
  have hH0 : 0 < Real.log (a / 2) := Real.log_pos hhalf
  have hcore : (1 + Real.log (a / 2)) * Real.log a ≤
      4 * (Real.log (a / 2)) ^ 2 := by
    calc
      (1 + Real.log (a / 2)) * Real.log a ≤
          (1 + Real.log (a / 2)) * (2 * Real.log (a / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (2 * Real.log (a / 2)) * (2 * Real.log (a / 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * (Real.log (a / 2)) ^ 2 := by ring
  refine ⟨hhalf, ?_⟩
  unfold activationDensity
  apply (div_le_div_iff₀
    (mul_pos (sq_pos_of_pos (by linarith : 0 < a / 2)) (sq_pos_of_pos hH0))
    (mul_pos (sq_pos_of_pos ha0) hL0)).mpr
  have hscaled := mul_le_mul_of_nonneg_left hcore (sq_nonneg a)
  convert hscaled using 1 <;> ring

/-- Half-scale stability, with a stronger domain than the closed interval
[a/2,2*a]: the upper endpoint restrictions are unnecessary. -/
theorem loglog_tangent_gap_stability_scaled {a x y : ℝ}
    (ha : Real.exp 2 ≤ a) (hx : a / 2 ≤ x) (hy : a / 2 ≤ y) :
    let K := fun z : ℝ => Real.log (Real.log a) + (z - a) / (a * Real.log a) -
      Real.log (Real.log z)
    let M := |x - y|
    let d := |y - a|
    |K x - K y| ≤ (16 / (a ^ 2 * Real.log a)) * (d * M + M ^ 2 / 2) := by
  have hh := density_half_le ha
  have hha : a / 2 ≤ a := by linarith [hh.1]
  have ha1 : 1 < a := hh.1.trans_le hha
  have hx1 : 1 < x := hh.1.trans_le hx
  have hy1 : 1 < y := hh.1.trans_le hy
  have hclower : a / 2 ≤ min a (min x y) := le_min hha (le_min hx hy)
  have hcoefficient : activationDensity (min a (min x y)) ≤
      16 / (a ^ 2 * Real.log a) :=
    (density_antitone hh.1 hclower).trans hh.2
  have hglobal := loglog_tangent_gap_stability ha1 hx1 hy1
  dsimp only at hglobal ⊢
  have hglobal' :
      |(Real.log (Real.log a) + (x - a) / (a * Real.log a) - Real.log (Real.log x)) -
        (Real.log (Real.log a) + (y - a) / (a * Real.log a) - Real.log (Real.log y))| ≤
      activationDensity (min a (min x y)) *
        (|y - a| * |x - y| + |x - y| ^ 2 / 2) := by
    simpa only [activationDensity, add_comm] using hglobal
  exact hglobal'.trans (mul_le_mul_of_nonneg_right hcoefficient (by positivity))

end D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
