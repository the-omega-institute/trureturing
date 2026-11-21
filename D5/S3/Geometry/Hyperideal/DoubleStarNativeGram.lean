/- GID: D5/S3/Geometry/Hyperideal/DoubleStarNativeGram
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/DoubleStarNativeGram
   mirror-E: none(waiver:exact-local-real-inequalities)
   anchors: []
   utility: none
   digest: Exact local real inequalities for CFMP opposite-edge transitions; no global geometric realization claimed. -/

import D5.S3.Geometry.Hyperideal.DoubleStarOpposite
import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

set_option autoImplicit false

/-! Native original Gram determinant for the double star.
No realization or shared-face manifold theorem is asserted. -/
noncomputable section
namespace D5.S3.Geometry.Hyperideal.DoubleStarNativeGram

open D5.S3.Geometry.Hyperideal.DoubleStarBernstein
open D5.S3.Geometry.Hyperideal.DoubleStarOpposite

open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

theorem chosenOpp_native_gram_negative (x a b c d : ℝ)
    (hx : 1 < x) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d)
    (ho : 1 < chosenOpp x a b c d) :
    (gram x a c (chosenOpp x a b c d) d b).det < 0 := by
  let o := chosenOpp x a b c d
  obtain ⟨⟨hD1,hD2⟩,_,hi⟩ := original_cosine_interface x a c o d b hx ha hc ho hd hb
  have hden_eq : denSq x a b c d = D1 x a b * D2 x c d := rfl
  have hden : 0 < denSq x a b c d := by rw [hden_eq]; exact mul_pos hD1 hD2
  have hD_ne : Real.sqrt (denSq x a b c d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hden)
  have hN := chosenOpp_rawCos hx hden
  change numerator x a b c d o / Real.sqrt (denSq x a b c d) = Real.sqrt 3 / 2 at hN
  have hN' := (div_eq_iff hD_ne).mp hN
  have hN_eq : N x a c o d b = numerator x a b c d o := by
    unfold N numerator
    ring
  have hN2 := congrArg (fun v : ℝ => v^2) hN'
  rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),
    Real.sq_sqrt hden.le] at hN2
  apply hi.mpr
  rw [hN_eq, ← hden_eq]
  linarith only [hN2, hden]

theorem first_native_gram_negative (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    (gram x (101/100) 500 (chosenOpp x (101/100) (3/2) 500 (101/100))
      (101/100) (3/2)).det < 0 := by
  have ho : 1 < chosenOpp x (101/100) (3/2) 500 (101/100) := by
    linarith only [(first_exact x hl hu).1]
  exact chosenOpp_native_gram_negative x (101/100) (3/2) 500 (101/100)
    (by linarith only [hl]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ho

theorem middle_native_gram_negative (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    (gram x 500 500 (chosenOpp x 500 (101/100) 500 (101/100))
      (101/100) (101/100)).det < 0 := by
  have ho : 1 < chosenOpp x 500 (101/100) 500 (101/100) := by
    linarith only [(middle_exact x hl hu).1]
  exact chosenOpp_native_gram_negative x 500 (101/100) 500 (101/100)
    (by linarith only [hl]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ho

theorem last_native_gram_negative (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    (gram x 500 (101/100) (chosenOpp x 500 (101/100) (101/100) (101/100))
      (101/100) (101/100)).det < 0 := by
  have ho : 1 < chosenOpp x 500 (101/100) (101/100) (101/100) := by
    linarith only [(last_exact x hl hu).1]
  exact chosenOpp_native_gram_negative x 500 (101/100) (101/100) (101/100)
    (by linarith only [hl]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ho


end D5.S3.Geometry.Hyperideal.DoubleStarNativeGram
