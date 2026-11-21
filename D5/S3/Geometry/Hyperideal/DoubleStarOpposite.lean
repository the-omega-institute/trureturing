/- GID: D5/S3/Geometry/Hyperideal/DoubleStarOpposite
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/DoubleStarOpposite
   mirror-E: none(waiver:exact-local-real-inequalities)
   anchors: []
   utility: none
   digest: Exact local real inequalities for CFMP opposite-edge transitions; no global geometric realization claimed. -/

import D5.S3.Geometry.Hyperideal.DoubleStarBernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false

/-! Positive opposite lengths and exact target angles for the double-star formulas.
Native tetrahedron, path gluing and existence of the seed A* are not assumed here. -/
noncomputable section

namespace D5.S3.Geometry.Hyperideal.DoubleStarOpposite

open D5.S3.Geometry.Hyperideal.DoubleStarBernstein


def chosenOpp (x a b c d : ℝ) : ℝ :=
  (numerator x a b c d 0 - Real.sqrt (3 * denSq x a b c d) / 2) / (x^2-1)

def rawCos (x a b c d o : ℝ) : ℝ :=
  numerator x a b c d o / Real.sqrt (denSq x a b c d)

private theorem x_square_gap {x : ℝ} (hx : 1 < x) : 0 < x^2-1 := by
  nlinarith only [sq_nonneg (x-1), hx]

private theorem rad_pos {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 0 < b) :
    0 < rad x a b := by
  have hx' : 0 < x := by linarith only [hx]
  have hm := mul_pos (mul_pos hx' ha) hb
  unfold rad
  nlinarith only [x_square_gap hx, hm, sq_nonneg a, sq_nonneg b]

private theorem den_pos {x a b c d : ℝ} (hx : 1 < x)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < denSq x a b c d :=
  mul_pos (rad_pos hx ha hb) (rad_pos hx hc hd)

private theorem numerator_affine (x a b c d o : ℝ) :
    numerator x a b c d o = numerator x a b c d 0 - (x^2-1)*o := by
  unfold numerator
  ring

theorem lt_chosenOpp_of_pos_margin {x a b c d o : ℝ} (hx : 1 < x)
    (hD : 0 ≤ denSq x a b c d)
    (hn : 0 < numerator x a b c d o) (hg : 0 < margin x a b c d o) :
    o < chosenOpp x a b c d := by
  have h₃ : 0 ≤ 3 * denSq x a b c d := by linarith only [hD]
  have hs := Real.sq_sqrt h₃
  have hsq : (Real.sqrt (3 * denSq x a b c d))^2 < (2 * numerator x a b c d o)^2 := by
    unfold margin at hg
    nlinarith only [hs, hg]
  have hn' : 0 ≤ 2 * numerator x a b c d o := by linarith only [hn]
  have h := (sq_lt_sq₀ (Real.sqrt_nonneg _) hn').mp hsq
  unfold chosenOpp
  apply (lt_div_iff₀ (x_square_gap hx)).mpr
  rw [numerator_affine] at h
  linarith only [h]

theorem chosenOpp_lt_of_neg_margin {x a b c d o : ℝ} (hx : 1 < x)
    (hD : 0 ≤ denSq x a b c d)
    (hn : 0 < numerator x a b c d o) (hg : margin x a b c d o < 0) :
    chosenOpp x a b c d < o := by
  have h₃ : 0 ≤ 3 * denSq x a b c d := by linarith only [hD]
  have hs := Real.sq_sqrt h₃
  have hsq : (2 * numerator x a b c d o)^2 < (Real.sqrt (3 * denSq x a b c d))^2 := by
    unfold margin at hg
    nlinarith only [hs, hg]
  have hn' : 0 ≤ 2 * numerator x a b c d o := by linarith only [hn]
  have h := (sq_lt_sq₀ hn' (Real.sqrt_nonneg _)).mp hsq
  unfold chosenOpp
  apply (div_lt_iff₀ (x_square_gap hx)).mpr
  rw [numerator_affine] at h
  linarith only [h]

theorem chosenOpp_rawCos {x a b c d : ℝ} (hx : 1 < x) (hD : 0 < denSq x a b c d) :
    rawCos x a b c d (chosenOpp x a b c d) = Real.sqrt 3 / 2 := by
  have hh : x^2-1 ≠ 0 := ne_of_gt (x_square_gap hx)
  have hs : Real.sqrt (denSq x a b c d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hD)
  have hnum : numerator x a b c d (chosenOpp x a b c d) =
      Real.sqrt (3 * denSq x a b c d) / 2 := by
    rw [numerator_affine, chosenOpp]
    field_simp
    ring
  rw [rawCos, hnum, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  field_simp

theorem chosenOpp_angle {x a b c d : ℝ} (hx : 1 < x) (hD : 0 < denSq x a b c d) :
    Real.arccos (rawCos x a b c d (chosenOpp x a b c d)) = Real.pi / 6 := by
  rw [chosenOpp_rawCos hx hD, ← Real.cos_pi_div_six]
  exact Real.arccos_cos (by linarith only [Real.pi_pos]) (by linarith only [Real.pi_pos])

theorem first_exact (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    6 < chosenOpp x (101/100) (3/2) 500 (101/100) ∧
    chosenOpp x (101/100) (3/2) 500 (101/100) < 30 ∧
    Real.arccos (rawCos x (101/100) (3/2) 500 (101/100)
      (chosenOpp x (101/100) (3/2) 500 (101/100))) = Real.pi / 6 := by
  have hx : 1 < x := by linarith only [hl]
  have hd := den_pos hx (by norm_num : (0:ℝ)<101/100) (by norm_num : (0:ℝ)<3/2)
    (by norm_num : (0:ℝ)<500) (by norm_num : (0:ℝ)<101/100)
  obtain ⟨hll, hlp⟩ := first_at_six x hl hu
  obtain ⟨hul, hup⟩ := first_at_thirty x hl hu
  exact ⟨lt_chosenOpp_of_pos_margin hx hd.le hll hlp,
    chosenOpp_lt_of_neg_margin hx hd.le hul hup, chosenOpp_angle hx hd⟩

theorem middle_exact (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    6 < chosenOpp x 500 (101/100) 500 (101/100) ∧
    chosenOpp x 500 (101/100) 500 (101/100) < 250 ∧
    Real.arccos (rawCos x 500 (101/100) 500 (101/100)
      (chosenOpp x 500 (101/100) 500 (101/100))) = Real.pi / 6 := by
  have hx : 1 < x := by linarith only [hl]
  have hd := den_pos hx (by norm_num : (0:ℝ)<500) (by norm_num : (0:ℝ)<101/100)
    (by norm_num : (0:ℝ)<500) (by norm_num : (0:ℝ)<101/100)
  obtain ⟨hll, hlp⟩ := middle_at_six x hl hu
  obtain ⟨hul, hup⟩ := middle_at_250 x hl hu
  exact ⟨lt_chosenOpp_of_pos_margin hx hd.le hll hlp,
    chosenOpp_lt_of_neg_margin hx hd.le hul hup, chosenOpp_angle hx hd⟩

theorem last_exact (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    2 < chosenOpp x 500 (101/100) (101/100) (101/100) ∧
    chosenOpp x 500 (101/100) (101/100) (101/100) < 6 ∧
    Real.arccos (rawCos x 500 (101/100) (101/100) (101/100)
      (chosenOpp x 500 (101/100) (101/100) (101/100))) = Real.pi / 6 := by
  have hx : 1 < x := by linarith only [hl]
  have hd := den_pos hx (by norm_num : (0:ℝ)<500) (by norm_num : (0:ℝ)<101/100)
    (by norm_num : (0:ℝ)<101/100) (by norm_num : (0:ℝ)<101/100)
  obtain ⟨hll, hlp⟩ := last_at_two x hl hu
  obtain ⟨hul, hup⟩ := last_at_six x hl hu
  exact ⟨lt_chosenOpp_of_pos_margin hx hd.le hll hlp,
    chosenOpp_lt_of_neg_margin hx hd.le hul hup, chosenOpp_angle hx hd⟩


end D5.S3.Geometry.Hyperideal.DoubleStarOpposite
