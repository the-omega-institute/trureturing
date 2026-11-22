/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMiddleGapHessianRule
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed directional Hessian bound for a centered rectangle. -/

module

public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Signed Hessian bounds along a segment -/

open Set

namespace RefinedBMV.PositiveCenter

/-- A directional Taylor value at the segment endpoint from the value, slope, and
half-second-derivative coefficients. The slope is taken within the closed segment. -/
public theorem exists_directionalTaylorValue {f : ℝ → ℝ} {value slope : ℝ}
    {quadratic : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hvalue : f 0 = value) (hslope : HasDerivWithinAt f slope (Icc 0 1) 0)
    (hquadratic : ∀ s ∈ Ioo (0 : ℝ) 1, deriv (deriv f) s / 2 = quadratic s) :
    ∃ s ∈ Ioo (0 : ℝ) 1, f 1 = value + slope + quadratic s := by
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  obtain ⟨s, hs, htaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (ne_of_lt h01) (by
      simpa only [uIcc_of_le h01.le, Nat.cast_one, one_add_one_eq_two] using hf)
  rw [uIoo_of_lt h01] at hs
  rw [uIcc_of_le h01.le] at htaylor
  have hd : iteratedDerivWithin 1 f (Icc 0 1) 0 = slope := by
    rw [iteratedDerivWithin_one]
    exact hslope.derivWithin (uniqueDiffOn_Icc h01 0 (by simp))
  have hpoly : taylorWithinEval f 1 (Icc 0 1) 0 1 = value + slope := by
    simp [taylorWithinEval_succ, hd, hvalue]
  rw [hpoly, iteratedDeriv_succ, iteratedDeriv_one] at htaylor
  norm_num [Nat.factorial] at htaylor
  exact ⟨s, hs, by linarith [hquadratic s hs]⟩

private theorem neg_mul_le_mul_of_abs_bounds {a b A B : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) : -(A * B) ≤ a * b := by
  have hab : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  exact neg_le_of_abs_le hab

private theorem signed_square_le {z r l H : ℝ} (hz : |z| ≤ r) (hl : l ≤ H) :
    min 0 l * r ^ 2 ≤ H * z ^ 2 := by
  have hsq : z ^ 2 ≤ r ^ 2 := sq_le_sq' (abs_le.mp hz).1 (abs_le.mp hz).2
  exact (mul_le_mul_of_nonpos_left hsq (min_le_left _ _)).trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans hl) (sq_nonneg _))

/-- The signed Hessian envelope along a displacement gives a uniform lower bound
using the two coordinate radii. The mixed coefficient includes the Taylor factor. -/
public theorem centeredHessianLowerBound {f : ℝ → ℝ}
    {x y rh rd v0 Gh Gd Mh Md lh ld Mhd : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hx : |x| ≤ rh) (hy : |y| ≤ rd) (hvalue : v0 ≤ f 0)
    (hslope : HasDerivWithinAt f (Gh * x + Gd * y) (Icc 0 1) 0)
    (hGh : |Gh| ≤ Mh) (hGd : |Gd| ≤ Md)
    (hHessian : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ Hhh Hhd Hdd : ℝ,
      deriv (deriv f) s / 2 = Hhh * x ^ 2 + Hhd * x * y + Hdd * y ^ 2 ∧
        lh ≤ Hhh ∧ |Hhd| ≤ Mhd ∧ ld ≤ Hdd) :
    v0 - Mh * rh - Md * rd + min 0 lh * rh ^ 2 - Mhd * rh * rd +
        min 0 ld * rd ^ 2 ≤ f 1 := by
  obtain ⟨s, hs, hTaylor⟩ := exists_directionalTaylorValue hf rfl hslope (fun _ _ ↦ rfl)
  obtain ⟨Hhh, Hhd, Hdd, hquad, hhh, hhd, hdd⟩ := hHessian s hs
  have hxy : |x * y| ≤ rh * rd := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  have hmix := neg_mul_le_mul_of_abs_bounds hhd hxy
  rw [← mul_assoc, ← mul_assoc] at hmix
  rw [hTaylor, hquad]
  linarith [neg_mul_le_mul_of_abs_bounds hGh hx, neg_mul_le_mul_of_abs_bounds hGd hy,
    signed_square_le hx hhh, signed_square_le hy hdd]

end RefinedBMV.PositiveCenter
