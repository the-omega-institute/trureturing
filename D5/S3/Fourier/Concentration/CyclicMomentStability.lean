/- GID: D5/S3/Fourier/Concentration/CyclicMomentStability
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicMomentStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound phase error and mass imbalance by the first two Fourier moments. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset

namespace D5.S3.Fourier.Concentration.CyclicMomentStability

private theorem first_moment_projection_variance
    {J : Type*} [Fintype J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hw : ∑ j, w j = 1) :
    let m := ∑ j, (w j : ℂ) * z j
    let c := ‖m‖ ^ 2
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    ∑ j, w j * ((star m * z j).re - c) ^ 2 = c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2 := by
  let m : ℂ := ∑ j, (w j : ℂ) * z j
  let c : ℝ := ‖m‖ ^ 2
  let X (j : J) := star m * z j
  let b := ∑ j, (w j : ℂ) * z j ^ 2
  change ∑ j, w j * ((X j).re - c) ^ 2 = c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
  have hcx : (c : ℂ) = star m * m := by
    simpa [c, Complex.ofReal_pow] using (Complex.conj_mul' m).symm
  have hcomplex : ∑ j, (w j : ℂ) * X j = (c : ℂ) := by
    rw [hcx]
    simp_rw [X, mul_left_comm (↑(w _) : ℂ) (star m), ← mul_sum]
    rfl
  have hfirstRe : ∑ j, w j * (X j).re = c := by
    simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re hcomplex
  have hsecondX : ∑ j, (w j : ℂ) * X j ^ 2 = star m ^ 2 * b := by
    simp_rw [X, mul_pow, mul_left_comm (↑(w _) : ℂ) (star m ^ 2), ← mul_sum]
    rfl
  have hsecondRe : ∑ j, w j * (X j ^ 2).re = (star m ^ 2 * b).re := by
    simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re hsecondX
  have hnorm (j : J) : Complex.normSq (X j) = c := by
    rw [Complex.normSq_eq_norm_sq]
    simp [X, hz, c]
  have hpoint (j : J) : (X j).re ^ 2 = (c + (X j ^ 2).re) / 2 := by
    have h := hnorm j
    rw [Complex.normSq_apply] at h
    have hp : (X j ^ 2).re =
        (X j).re * (X j).re - (X j).im * (X j).im := by
      rw [pow_two, Complex.mul_re]
    nlinarith only [h, hp]
  have hsecondReal : ∑ j, w j * (X j).re ^ 2 = c / 2 + (star m ^ 2 * b).re / 2 := by
    calc
      _ = ∑ j, (w j * c + w j * (X j ^ 2).re) / 2 := by
        exact sum_congr rfl fun j _ => by rw [hpoint]; ring
      _ = c / 2 + (star m ^ 2 * b).re / 2 := by
        simp_rw [div_eq_mul_inv, ← sum_mul, sum_add_distrib, ← sum_mul, hw, hsecondRe]
        ring
  calc
    _ = ∑ j, (w j * (X j).re ^ 2 - (2 * c) * (w j * (X j).re) + w j * c ^ 2) :=
      sum_congr rfl fun j _ => by ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hfirstRe, hsecondReal, hw]
      ring

private theorem imaginary_magnitude_error
    {x y c t : ℝ} (hc : 0 < c) (hc' : c < 1) (ht : 0 < t)
    (hphase : x ^ 2 + y ^ 2 = c) (hs : t ^ 2 = c - c ^ 2) :
    (|y| - t) ^ 2 ≤ (4 / t ^ 2) * (x - c) ^ 2 := by
  have hx : |x| ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one x).mp
    nlinarith [sq_nonneg y]
  have hxc : |x + c| ≤ 2 := calc
    _ ≤ |x| + |c| := abs_add_le _ _
    _ ≤ 2 := by rw [abs_of_pos hc]; linarith
  have hfactor : (|y| - t) * (|y| + t) = (c - x) * (c + x) := by
    nlinarith [sq_abs y]
  have hsum : 0 ≤ |y| + t := add_nonneg (abs_nonneg _) ht.le
  have habs : abs (|y| - t) * (|y| + t) = |x - c| * |x + c| := by
    have h := congrArg abs hfactor
    rw [abs_mul, abs_of_nonneg hsum, abs_mul, abs_sub_comm c x, add_comm c x] at h
    exact h
  have hproduct : t * abs (|y| - t) ≤ 2 * |x - c| := calc
    _ ≤ (|y| + t) * abs (|y| - t) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg y)) (abs_nonneg _)
    _ = |x - c| * |x + c| := (mul_comm _ _).trans habs
    _ ≤ 2 * |x - c| := by
      rw [mul_comm (2 : ℝ)]
      exact mul_le_mul_of_nonneg_left hxc (abs_nonneg _)
  have hsq := pow_le_pow_left₀ (mul_nonneg ht.le (abs_nonneg _)) hproduct 2
  rw [mul_pow, mul_pow, sq_abs, sq_abs] at hsq
  calc
    _ ≤ (2 ^ 2 * (x - c) ^ 2) / t ^ 2 :=
      (le_div_iff₀ (pow_pos ht 2)).mpr (by simpa only [mul_comm] using hsq)
    _ = _ := by norm_num; ring

private theorem contact_and_balance {J : Type*} [Fintype J]
    (w x y : J → ℝ) (hw : ∑ j, w j = 1) (hpos : ∀ j, 0 ≤ w j)
    {c t : ℝ} (hc : 0 < c) (hc' : c < 1) (ht : 0 < t) (hs : t ^ 2 = c - c ^ 2)
    (hphase : ∀ j, x j ^ 2 + y j ^ 2 = c) (hzero : ∑ j, w j * y j = 0) :
    let η (j : J) : ℝ := if 0 ≤ y j then 1 else -1
    let D := ∑ j, w j * (x j - c) ^ 2
    (∑ j, w j * ((x j - c) ^ 2 + (y j - η j * t) ^ 2)) ≤ (1 + 4 / t ^ 2) * D ∧
      (∑ j, w j * η j) ^ 2 ≤ 4 * D / t ^ 4 := by
  dsimp only
  let η (j : J) : ℝ := if 0 ≤ y j then 1 else -1
  let D := ∑ j, w j * (x j - c) ^ 2
  have hpoint (j : J) : (y j - η j * t) ^ 2 ≤ (4 / t ^ 2) * (x j - c) ^ 2 := by
    have hsigned : (y j - η j * t) ^ 2 = (|y j| - t) ^ 2 := by
      by_cases hy : 0 ≤ y j
      · simp [η, hy, abs_of_nonneg hy]
      · simp [η, hy, abs_of_neg (lt_of_not_ge hy)]
        ring
    rw [hsigned]
    exact imaginary_magnitude_error hc hc' ht (hphase j) hs
  have hsum : (∑ j, w j * (y j - η j * t) ^ 2) ≤ (4 / t ^ 2) * D := calc
    _ ≤ ∑ j, w j * ((4 / t ^ 2) * (x j - c) ^ 2) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hpos j)
    _ = _ := by
      unfold D
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
  change (∑ j, w j * ((x j - c) ^ 2 + (y j - η j * t) ^ 2)) ≤ (1 + 4 / t ^ 2) * D ∧
    (∑ j, w j * η j) ^ 2 ≤ 4 * D / t ^ 4
  constructor
  · simp_rw [mul_add, sum_add_distrib]
    change D + ∑ j, w j * (y j - η j * t) ^ 2 ≤ (1 + 4 / t ^ 2) * D
    linarith only [hsum]
  · have hcauchy := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset J)
        (r := fun j => w j * (y j - η j * t)) (f := w)
        (g := fun j => w j * (y j - η j * t) ^ 2)
        (fun j _ => hpos j) (fun j _ => mul_nonneg (hpos j) (sq_nonneg _))
        (fun j _ => le_of_eq (by ring))
    rw [hw, one_mul] at hcauchy
    have hlinear : (∑ j, w j * (y j - η j * t)) = -(∑ j, w j * η j) * t := by
      simp_rw [mul_sub, ← mul_assoc]
      rw [sum_sub_distrib, hzero, ← sum_mul, zero_sub, neg_mul]
    rw [hlinear, mul_pow, neg_sq] at hcauchy
    apply (le_div_iff₀ (pow_pos ht 4)).mpr
    have h := mul_le_mul_of_nonneg_right (hcauchy.trans hsum) (sq_nonneg t)
    have hcancel : 4 / t ^ 2 * D * t ^ 2 = 4 * D := by field_simp
    rw [hcancel] at h
    simpa only [mul_assoc, ← pow_add] using h

/-- The difference between the first two complex moments controls the weighted error
to the two possible phase contacts and the imbalance of their masses. -/
theorem first_two_moment_stability {J : Type*} [Fintype J]
    (z : J → ℂ) (w : J → ℝ) (hz : ∀ j, ‖z j‖ = 1)
    (hw : ∑ j, w j = 1) (hpos : ∀ j, 0 ≤ w j) :
    let m := ∑ j, (w j : ℂ) * z j
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    let c := ‖m‖ ^ 2
    let X (j : J) := star m * z j
    let t := Real.sqrt (c * (1 - c))
    let η (j : J) : ℝ := if 0 ≤ (X j).im then 1 else -1
    let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
    0 < c → c < 1 →
      (∑ j, w j * ‖X j - (c : ℂ) - (↑(η j * t) : ℂ) * Complex.I‖ ^ 2) ≤
        (1 + 4 / t ^ 2) * D ∧ (∑ j, w j * η j) ^ 2 ≤ 4 * D / t ^ 4 := by
  dsimp only
  let m := ∑ j, (w j : ℂ) * z j
  let b := ∑ j, (w j : ℂ) * z j ^ 2
  let c := ‖m‖ ^ 2
  let X (j : J) := star m * z j
  let t := Real.sqrt (c * (1 - c))
  let η (j : J) : ℝ := if 0 ≤ (X j).im then 1 else -1
  let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
  change 0 < c → c < 1 →
    (∑ j, w j * ‖X j - (c : ℂ) - (↑(η j * t) : ℂ) * Complex.I‖ ^ 2) ≤
      (1 + 4 / t ^ 2) * D ∧ (∑ j, w j * η j) ^ 2 ≤ 4 * D / t ^ 4
  intro hc hc'
  have ht : 0 < t := Real.sqrt_pos.2 (mul_pos hc (sub_pos.mpr hc'))
  have hs : t ^ 2 = c - c ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg hc.le (sub_nonneg.mpr hc'.le))]
    ring
  have hphase (j : J) : (X j).re ^ 2 + (X j).im ^ 2 = c := by
    have hnorm : Complex.normSq (X j) = c := by
      rw [Complex.normSq_eq_norm_sq]
      simp [X, hz, c]
    rw [Complex.normSq_apply] at hnorm
    simpa only [pow_two] using hnorm
  have hmean : ∑ j, (w j : ℂ) * X j = (c : ℂ) := by
    rw [show (c : ℂ) = star m * m by
      simpa [c, Complex.ofReal_pow] using (Complex.conj_mul' m).symm]
    simp_rw [X, mul_left_comm (↑(w _) : ℂ) (star m), ← mul_sum]
    rfl
  have hzero : ∑ j, w j * (X j).im = 0 := by
    simpa [Complex.im_sum, Complex.mul_im] using congrArg Complex.im hmean
  have hvar : ∑ j, w j * ((X j).re - c) ^ 2 = D :=
    first_moment_projection_variance z w hz hw
  have h := contact_and_balance w (fun j => (X j).re) (fun j => (X j).im)
    hw hpos hc hc' ht hs hphase hzero
  change (∑ j, w j * (((X j).re - c) ^ 2 + ((X j).im - η j * t) ^ 2)) ≤
      (1 + 4 / t ^ 2) * (∑ j, w j * ((X j).re - c) ^ 2) ∧
    (∑ j, w j * η j) ^ 2 ≤ 4 * (∑ j, w j * ((X j).re - c) ^ 2) / t ^ 4 at h
  rw [hvar] at h
  refine ⟨?_, h.2⟩
  have hnorm (j : J) : ‖X j - (c : ℂ) - (↑(η j * t) : ℂ) * Complex.I‖ ^ 2 =
      ((X j).re - c) ^ 2 + ((X j).im - η j * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, pow_two]
  simpa only [hnorm] using h.1

end D5.S3.Fourier.Concentration.CyclicMomentStability
