/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The existing Perron logarithm fixes the Gaussian crossing and quantitative slope bounds. -/

import D5.S0.Tower.DBonacci.PerronRoot
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic



/-! The scale is fixed by the existing order-nine Perron instance. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot

open Set
open D5.S0.Tower.DBonacci.PerronRoot

noncomputable def gaussian (s : ℝ) : ℝ := Real.exp s + Real.exp (-9 * s)

private theorem hasDerivAt_gaussian (s : ℝ) :
    HasDerivAt gaussian (Real.exp s - 9 * Real.exp (-9 * s)) s := by
  have hlinear : HasDerivAt (fun x : ℝ => -9 * x) (-9) s :=
    hasDerivAt_const_mul (x := s) (-9)
  convert (Real.hasDerivAt_exp s).add hlinear.exp using 1 <;>
    (try funext x) <;> (try simp only [gaussian, Pi.add_apply]) <;> ring

private theorem differentiable_gaussian : Differentiable ℝ gaussian :=
  fun s => (hasDerivAt_gaussian s).differentiableAt

private theorem continuous_gaussian : Continuous gaussian :=
  differentiable_gaussian.continuous

private theorem twentyfive_le_exp_six : (25 : ℝ) ≤ Real.exp 6 := by
  have h := Real.sum_le_exp_of_nonneg (x := (6 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact h

private theorem exp_neg_nine_mul_le {s : ℝ} (hs : (2 / 3 : ℝ) ≤ s) :
    Real.exp (-9 * s) ≤ 1 / 25 := by
  have h : (25 : ℝ) ≤ Real.exp (9 * s) :=
    twentyfive_le_exp_six.trans (Real.exp_le_exp.mpr (by linarith))
  rw [show -9 * s = -(9 * s) by ring, Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos (9 * s))).2
  linarith only [h]

private theorem gaussian_deriv_lower {s : ℝ} (hs : (2 / 3 : ℝ) ≤ s) :
    (98 / 75 : ℝ) ≤ deriv gaussian s := by
  rw [(hasDerivAt_gaussian s).deriv]
  have hpos := Real.add_one_le_exp s
  have hneg := exp_neg_nine_mul_le hs
  linarith only [hs, hpos, hneg]

/-- Quantitative growth on the entire relevant ray, including equal endpoints. -/
theorem gaussian_secant {a b : ℝ} (ha : (2 / 3 : ℝ) ≤ a) (hab : a ≤ b) :
    gaussian a + (98 / 75 : ℝ) * (b - a) ≤ gaussian b := by
  have hbound : ∀ x ∈ interior (Ici (2 / 3 : ℝ)),
      (98 / 75 : ℝ) ≤ deriv gaussian x := by
    intro x hx
    exact gaussian_deriv_lower (interior_subset hx)
  have h := (convex_Ici (2 / 3 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    continuous_gaussian.continuousOn differentiable_gaussian.differentiableOn hbound
    a ha b (ha.trans hab) hab
  linarith only [h]

theorem gaussian_strictMonoOn : StrictMonoOn gaussian (Ici (2 / 3 : ℝ)) := by
  intro a ha b _ hab
  have h := gaussian_secant ha hab.le
  have hpos : 0 < (98 / 75 : ℝ) * (b - a) :=
    mul_pos (by norm_num) (sub_pos.mpr hab)
  linarith only [h, hpos]

private theorem exp_two_thirds_lt : Real.exp (2 / 3 : ℝ) < 39 / 20 := by
  have h := Real.exp_bound' (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem gaussian_two_thirds_lt_two : gaussian (2 / 3) < 2 := by
  have hneg : Real.exp (-6 : ℝ) < 1 / 20 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 6)).2
    linarith only [twentyfive_le_exp_six]
  have hpos := exp_two_thirds_lt
  norm_num [gaussian]
  linarith only [hpos, hneg]

/-- The five terms through degree four already certify this strict endpoint. -/
private theorem gaussian_twentyfive_thirtysix_gt_two : (2 : ℝ) < gaussian (25 / 36) := by
  have h := Real.sum_le_exp_of_nonneg (x := (25 / 36 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hneg := Real.exp_pos (-9 * (25 / 36 : ℝ))
  unfold gaussian
  linarith only [h, hneg]

/-- Convexity rules out an additional positive root below the monotonicity ray. -/
private theorem gaussian_lt_two_of_pos_of_le_two_thirds {s : ℝ}
    (hs : 0 < s) (hs' : s ≤ (2 / 3 : ℝ)) : gaussian s < 2 := by
  have ha : 0 ≤ 1 - (3 / 2 : ℝ) * s := by linarith only [hs']
  have hb : 0 ≤ (3 / 2 : ℝ) * s := by linarith only [hs]
  have hab : (1 - (3 / 2 : ℝ) * s) + (3 / 2 : ℝ) * s = 1 := by ring
  have hfirst := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (2 / 3 : ℝ)) ha hb hab
  have hsecond := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-6 : ℝ)) ha hb hab
  have heq₁ : (1 - (3 / 2 : ℝ) * s) * 0 + ((3 / 2 : ℝ) * s) * (2 / 3) = s := by
    ring
  have heq₂ : (1 - (3 / 2 : ℝ) * s) * 0 + ((3 / 2 : ℝ) * s) * (-6) = -9 * s := by
    ring
  simp only [smul_eq_mul, heq₁, heq₂, Real.exp_zero, mul_one] at hfirst hsecond
  have hend := gaussian_two_thirds_lt_two
  norm_num [gaussian] at hend
  have hstrict := mul_pos (show 0 < (3 / 2 : ℝ) * s by linarith only [hs])
    (show 0 < 2 - (Real.exp (2 / 3 : ℝ) + Real.exp (-6 : ℝ)) by linarith only [hend])
  unfold gaussian
  nlinarith only [hfirst, hsecond, hstrict]

/-- The Gaussian root uses the existing order-nine Perron root, without a new choice. -/
noncomputable def s_star : ℝ := Real.log (dbonacciPerronRoot 9)

private theorem s_star_pos : 0 < s_star :=
  Real.log_pos (one_lt_dbonacciPerronRoot 9 (by norm_num))

theorem gaussian_s_star : gaussian s_star = 2 := by
  have hβ : 0 < dbonacciPerronRoot 9 :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num))
  have hmul : Real.exp (9 * Real.log (dbonacciPerronRoot 9)) =
      (dbonacciPerronRoot 9) ^ 9 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hβ] using
      Real.exp_nat_mul (Real.log (dbonacciPerronRoot 9)) 9
  have hroot := two_sub_dbonacciPerronRoot_eq_inv_pow 9 (by norm_num)
  unfold gaussian s_star
  rw [Real.exp_log hβ,
    show -9 * Real.log (dbonacciPerronRoot 9) =
      -(9 * Real.log (dbonacciPerronRoot 9)) by ring,
    Real.exp_neg, hmul, ← inv_pow]
  linarith only [hroot]

theorem two_thirds_lt_s_star : (2 / 3 : ℝ) < s_star := by
  by_contra h
  have hbad := gaussian_lt_two_of_pos_of_le_two_thirds s_star_pos (le_of_not_gt h)
  rw [gaussian_s_star] at hbad
  exact (lt_irrefl (2 : ℝ)) hbad

private theorem s_star_lt_twentyfive_thirtysix : s_star < (25 / 36 : ℝ) := by
  by_contra h
  have hle : (25 / 36 : ℝ) ≤ s_star := le_of_not_gt h
  have hsec := gaussian_secant (by norm_num : (2 / 3 : ℝ) ≤ 25 / 36) hle
  rw [gaussian_s_star] at hsec
  linarith only [hle, hsec, gaussian_twentyfive_thirtysix_gt_two]

noncomputable def alpha : ℝ := 2 / (3 * s_star)

private theorem three_mul_s_star_pos : 0 < 3 * s_star := by
  linarith only [two_thirds_lt_s_star]

theorem alpha_gt_twentyfour_twentyfive : (24 / 25 : ℝ) < alpha := by
  unfold alpha
  apply (lt_div_iff₀ three_mul_s_star_pos).2
  linarith only [s_star_lt_twentyfive_thirtysix]

theorem alpha_lt_one : alpha < 1 := by
  unfold alpha
  apply (div_lt_iff₀ three_mul_s_star_pos).2
  linarith only [two_thirds_lt_s_star]

end D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
