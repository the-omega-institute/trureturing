/- GID: D5/S3/Fourier/HexagonalThetaMinimum
   generality: G
   mirror-B: D5/B/S3/Fourier/HexagonalThetaMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict height monotonicity and the unique reduced minimum of planar theta. -/

import D5.S3.Fourier.ThetaVerticalPositive
import D5.S3.Fourier.ThetaShearMonotonicity

/-! # The unique minimum on the reduced theta strip -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Topology
open Filter

namespace D5.S3.Fourier.PlanarTheta
noncomputable section

private def verticalTail (y : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) ^ 2 *
    Real.exp (-Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3))

private def verticalRow (t y : ℝ) (n : ℤ) : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * (t / y) * ((m : ℝ) + (n : ℝ) / 2) ^ 2)

private lemma height_bounds {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) :
    5 / 6 < y ∧ 4 / 5 < y ∧ 4 / 5 < Real.sqrt y ∧ 3 / 4 ≤ y ^ 2 := by
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc0 := Real.sqrt_nonneg (3 : ℝ)
  have hy0 : 0 < y := (by positivity : 0 < Real.sqrt 3 / 2).trans_le hy
  have hs := Real.sq_sqrt hy0.le
  have hs0 := Real.sqrt_nonneg y
  have hysq : 3 / 4 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ y + Real.sqrt 3 / 2 by positivity)]
  have hylarge : 4 / 5 < y := by nlinarith
  refine ⟨by nlinarith, hylarge, ?_, hysq⟩
  by_contra h
  have hle : Real.sqrt y ≤ 4 / 5 := not_lt.mp h
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ 4 / 5 + Real.sqrt y by positivity)]

private lemma nat_gaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ => Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2)) := by
  simpa only [pow_zero, one_mul] using gaussian_moment ha 0

private lemma theta_zero_int {a : ℝ} (ha : 0 < a) :
    thetaFourier a 0 = ∑' m : ℤ, Real.exp (-Real.pi * a * (m : ℝ) ^ 2) := by
  simpa only [mul_zero, Real.cos_zero, mul_one] using (real_fourier_int ha 0).symm

private lemma theta_le_zero {a : ℝ} (ha : 0 < a) (b : ℝ) :
    thetaFourier a b ≤ thetaFourier a 0 := by
  have h := nat_gaussian_summable ha
  have hc := cos_summable ha b
  have hm : (∑' k : ℕ, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) *
      Real.cos (2 * Real.pi * ((k : ℝ) + 1) * b)) ≤
      ∑' k : ℕ, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
    apply hc.tsum_le_tsum _ h
    intro k
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
  linarith

private lemma theta_zero_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    thetaFourier b 0 ≤ thetaFourier a 0 := by
  have hb : 0 < b := ha.trans_le hab
  have hm : (∑' k : ℕ, Real.exp (-Real.pi * b * ((k : ℝ) + 1) ^ 2)) ≤
      ∑' k : ℕ, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
    apply (nat_gaussian_summable hb).tsum_le_tsum _ (nat_gaussian_summable ha)
    intro k
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hab
      (show 0 ≤ Real.pi * ((k : ℝ) + 1) ^ 2 by positivity)
    nlinarith only [h]
  simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
  linarith

private lemma theta_zero_pos {a : ℝ} (ha : 0 < a) : 0 < thetaFourier a 0 := by
  rw [theta_zero_int ha]
  have hs : Summable (fun m : ℤ => Real.exp (-Real.pi * a * (m : ℝ) ^ 2)) := by
    simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero, mul_assoc] using
      summable_pow_mul_jacobiTheta₂_term_bound 0 ha 0
  exact hs.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (by norm_num)

private lemma theta_height_bound {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) :
    thetaFourier y 0 < 4 / 3 := by
  have hys := height_bounds hy
  have hy0 : 0 < y := by linarith [hys.1]
  let q := Real.exp (-Real.pi * y)
  have hp : (5 : ℝ) / 2 < Real.pi * y := by
    have h := mul_lt_mul_of_pos_right Real.pi_gt_three hy0
    nlinarith [hys.1]
  have he : (8 : ℝ) < Real.exp (5 / 2) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq : q < 1 / 8 := by
    have hh := he.trans (Real.exp_lt_exp.mpr hp)
    dsimp [q]
    rw [show -Real.pi * y = -(Real.pi * y) by ring, Real.exp_neg, inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hb := HurwitzKernelBounds.F_nat_zero_le (a := 1) (by norm_num) hy0
  have heq : HurwitzKernelBounds.F_nat 0 1 y =
      ∑' k : ℕ, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * y) := by
    unfold HurwitzKernelBounds.F_nat
    apply tsum_congr
    intro k
    simp only [HurwitzKernelBounds.f_nat, pow_zero, one_mul]
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))] at hb
  norm_num only [one_pow, mul_one] at hb
  have hsum : (∑' k : ℕ, Real.exp (-Real.pi * y * ((k : ℝ) + 1) ^ 2)) ≤
      q / (1 - q) := by
    simpa only [mul_right_comm (-Real.pi)] using hb
  have hfrac : q / (1 - q) < 1 / 6 :=
    (div_lt_iff₀ (by linarith : 0 < 1 - q)).mpr (by linarith)
  simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
  linarith

private lemma vertical_tail_bound {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3))) ∧ verticalTail y < 1 / 10 := by
  have hys := height_bounds hy
  have hy0 : 0 < y := by linarith [hys.1]
  have hv : 1 / 2 ≤ (8 / 9 : ℝ) * y := by linarith [hys.1]
  have hm (k : ℕ) : ((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3)) ≤
      ((k : ℝ) + 2) ^ 2 *
        Real.exp (-Real.pi * ((8 / 9 : ℝ) * y) * (((k : ℝ) + 2) ^ 2 - 1)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpoly : (8 / 9 : ℝ) * (((k : ℝ) + 2) ^ 2 - 1) ≤
        ((k : ℝ) + 2) ^ 2 - 4 / 3 := by nlinarith [sq_nonneg (k : ℝ)]
    have h := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ Real.pi * y by positivity)
    nlinarith only [h]
  have hsum := (gaussian_tail_bound hv).1.of_nonneg_of_le (fun _ => by positivity) hm
  refine ⟨hsum, ?_⟩
  have hbound : verticalTail y ≤ gaussianTail ((8 / 9 : ℝ) * y) :=
    hsum.tsum_le_tsum hm (gaussian_tail_bound hv).1
  exact (hbound.trans_lt (gaussian_tail_bound hv).2.2).trans (by norm_num)

private lemma row_summable {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (n : ℤ) :
    Summable (fun m : ℤ => Real.exp (-Real.pi * (t / y) *
      ((m : ℝ) + (n : ℝ) / 2) ^ 2)) := by
  have hsource : Summable (fun m : ℤ => Real.exp (-Real.pi * t * Q (1 / 2) y (m, n))) := by
    have h := (summable t (1 / 2) ht hy).prod_symm.prod_factor n
    change Summable (fun m : ℤ => Real.exp (-Real.pi * t * Q (1 / 2) y (m, n))) at h
    exact h
  have h := hsource.mul_left (Real.exp (Real.pi * t * y * (n : ℝ) ^ 2))
  convert h using 1
  ext m
  rw [← Real.exp_add]
  congr 1
  dsimp [Q]
  field_simp [ht.ne', hy.ne']
  <;> ring

private lemma row_le_center {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (n : ℤ) :
    verticalRow t y n ≤ thetaFourier (t / y) 0 := by
  have hs : 0 < y / t := div_pos hy ht
  have hsz := (Real.sqrt_pos.mpr hs).ne'
  have he : verticalRow t y n = Real.sqrt (y / t) *
      thetaFourier (y / t) (-(n : ℝ) / 2) := by
    rw [thetaFourier_poisson hs]
    dsimp [verticalRow]
    rw [mul_inv_cancel_left₀ hsz]
    apply tsum_congr
    intro m
    congr 1
    field_simp [ht.ne', hy.ne']
    <;> ring
  have hc : thetaFourier (t / y) 0 =
      Real.sqrt (y / t) * thetaFourier (y / t) 0 := by
    rw [thetaFourier_zero_duality (div_pos ht hy)]
    simp only [inv_div]
    rw [show t / y = (y / t)⁻¹ by rw [inv_div], Real.sqrt_inv, inv_inv]
  rw [he, hc]
  exact mul_le_mul_of_nonneg_left (theta_le_zero hs _) (Real.sqrt_nonneg _)

private lemma theta_parameter_bound {t y : ℝ} (ht : 1 ≤ t) (hy : 0 < y) :
    thetaFourier (t / y) 0 ≤ Real.sqrt y * thetaFourier y 0 := by
  have hab : 1 / y ≤ t / y := div_le_div_of_nonneg_right ht hy.le
  have h := theta_zero_antitone (by positivity : 0 < 1 / y) hab
  have he : thetaFourier (1 / y) 0 = Real.sqrt y * thetaFourier y 0 := by
    rw [thetaFourier_zero_duality (by positivity : 0 < 1 / y)]
    simp only [one_div, inv_inv, Real.sqrt_inv]
  rw [he] at h
  exact h

private lemma half_row_bound {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    Real.exp (Real.pi * t / (4 * y)) * verticalRow t y 1 ≤
      1 + thetaFourier (t / y) 0 := by
  let a := t / y
  let f (m : ℤ) := Real.exp (-Real.pi * a * ((m : ℝ) * ((m : ℝ) + 1)))
  have ha : 0 < a := div_pos ht hy
  have hf : Summable f := by
    have h := (row_summable ht hy 1).mul_left (Real.exp (Real.pi * t / (4 * y)))
    convert h using 1
    ext m
    rw [← Real.exp_add]
    congr 1
    dsimp [f, a]
    norm_num only [Int.cast_one]
    field_simp [ht.ne', hy.ne']
    <;> ring
  have hp : Summable (fun k : ℕ => f k) :=
    hf.comp_injective (fun b c : ℕ => Int.ofNat_inj.mp)
  have heven : (fun k : ℕ => f (-(k + 1))) = (fun k : ℕ => f k) := by
    funext k
    dsimp [f]
    push_cast
    congr 1
    ring
  have hg : Summable (fun k : ℕ => Real.exp (-Real.pi * a * (k : ℝ) ^ 2)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using nat_gaussian_summable ha
  have hm : (∑' k : ℕ, f k) ≤ ∑' k : ℕ, Real.exp (-Real.pi * a * (k : ℝ) ^ 2) := by
    apply hp.tsum_le_tsum _ hg
    intro k
    apply Real.exp_le_exp.mpr
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    simp only [Int.cast_natCast]
    nlinarith [mul_nonneg (show 0 ≤ Real.pi * a by positivity) hk]
  have hsplit := hg.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero, Nat.cast_add, Nat.cast_one] at hsplit
  have he : Real.exp (Real.pi * t / (4 * y)) * verticalRow t y 1 =
      ∑' m : ℤ, f m := by
    rw [verticalRow, ← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [← Real.exp_add]
    congr 1
    dsimp [f, a]
    norm_num only [Int.cast_one]
    field_simp [ht.ne', hy.ne']
    <;> ring
  rw [he, tsum_of_nat_of_neg_add_one hp (heven.symm ▸ hp), heven]
  have hz : thetaFourier a 0 = 1 + 2 *
      ∑' k : ℕ, Real.exp (-Real.pi * a * ((k : ℝ) + 1) ^ 2) := by
    simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
  change _ ≤ 1 + thetaFourier a 0
  rw [hz]
  linarith

private def normalizedRow (t y : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2 *
    Real.exp (-Real.pi * t * y * (((k : ℝ) + 1) ^ 2 - 1) + Real.pi * t / (4 * y)) *
    verticalRow t y (k + 1)

private lemma normalized_row_tail {t y : ℝ} (ht : 1 ≤ t)
    (hy : Real.sqrt 3 / 2 ≤ y) (k : ℕ) :
    normalizedRow t y (k + 1) ≤ thetaFourier (t / y) 0 *
      (((k : ℝ) + 2) ^ 2 *
        Real.exp (-Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3))) := by
  have hys := height_bounds hy
  have hy0 : 0 < y := by linarith [hys.1]
  have ht0 : 0 < t := by linarith
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hinv : 1 / (4 * y) ≤ y / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * y)).mpr
    nlinarith [hys.2.2.2]
  have he : -Real.pi * t * y * (((k : ℝ) + 2) ^ 2 - 1) + Real.pi * t / (4 * y) ≤
      -Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3) := by
    have h1 : Real.pi * t / (4 * y) ≤ Real.pi * t * y / 3 := by
      convert mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ Real.pi * t by positivity) using 1 <;> ring
    have hn : 0 ≤ ((k : ℝ) + 2) ^ 2 - 4 / 3 := by
      nlinarith [sq_nonneg (k : ℝ)]
    have h2 := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3) by positivity)
    nlinarith only [h1, h2]
  have h := mul_le_mul (Real.exp_le_exp.mpr he)
    (row_le_center ht0 hy0 ((k + 1 : ℕ) + 1))
    (by dsimp [verticalRow]; positivity) (by positivity : 0 ≤ Real.exp _)
  have h := mul_le_mul_of_nonneg_left h (sq_nonneg ((k : ℝ) + 2))
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  dsimp [normalizedRow]
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
  convert h using 1 <;> ring

private lemma normalized_rows_bound {t y : ℝ} (ht : 1 ≤ t)
    (hy : Real.sqrt 3 / 2 ≤ y) : Summable (normalizedRow t y) ∧
    (∑' k : ℕ, normalizedRow t y k) ≤
      1 + thetaFourier (t / y) 0 * (1 + verticalTail y) := by
  have hys := height_bounds hy
  have hy0 : 0 < y := by linarith [hys.1]
  have ht0 : 0 < t := by linarith
  have htθ : 0 < thetaFourier (t / y) 0 := theta_zero_pos (div_pos ht0 hy0)
  have htail : Summable (fun k : ℕ => normalizedRow t y (k + 1)) :=
    ((vertical_tail_bound hy).1.mul_left (thetaFourier (t / y) 0)).of_nonneg_of_le
      (fun k => by dsimp [normalizedRow, verticalRow]; positivity)
      (normalized_row_tail ht hy)
  have hfull : Summable (normalizedRow t y) := (summable_nat_add_iff 1).mp htail
  refine ⟨hfull, ?_⟩
  have hb : (∑' k : ℕ, normalizedRow t y (k + 1)) ≤
      thetaFourier (t / y) 0 * verticalTail y := by
    calc
      _ ≤ ∑' k : ℕ, thetaFourier (t / y) 0 * (((k : ℝ) + 2) ^ 2 *
          Real.exp (-Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3))) :=
        htail.tsum_le_tsum (normalized_row_tail ht hy)
          ((vertical_tail_bound hy).1.mul_left _)
      _ = _ := by rw [tsum_mul_left]; rfl
  have hfirst : normalizedRow t y 0 ≤ 1 + thetaFourier (t / y) 0 := by
    simpa only [normalizedRow, Nat.cast_zero, zero_add, one_pow, sub_self,
      mul_zero, zero_add, one_mul, Nat.zero_add] using half_row_bound ht0 hy0
  rw [← hfull.sum_add_tsum_nat_add 1, Finset.sum_range_one]
  nlinarith only [hb, hfirst]

private lemma normalized_numeric_bound {t y : ℝ} (ht : 1 ≤ t)
    (hy : Real.sqrt 3 / 2 ≤ y) :
    (2 / y) * (∑' k : ℕ, normalizedRow t y k) < 91 / 15 := by
  have hys := height_bounds hy
  have hy0 : 0 < y := by linarith [hys.1]
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have htθ : 0 < thetaFourier y 0 := theta_zero_pos hy0
  have hT : 0 ≤ verticalTail y := by
    change 0 ≤ ∑' k : ℕ, ((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * y * (((k : ℝ) + 2) ^ 2 - 4 / 3))
    exact tsum_nonneg (fun k => by positivity)
  have hbound := (normalized_rows_bound ht hy).2
  have hparameter := theta_parameter_bound ht hy0
  have hsum : (∑' k : ℕ, normalizedRow t y k) ≤
      1 + Real.sqrt y * thetaFourier y 0 * (1 + verticalTail y) := by
    have h := mul_le_mul_of_nonneg_right hparameter (show 0 ≤ 1 + verticalTail y by positivity)
    linarith
  have hprod : thetaFourier y 0 * (1 + verticalTail y) < 22 / 15 := by
    calc
      _ < thetaFourier y 0 * (11 / 10) :=
        mul_lt_mul_of_pos_left (by linarith [(vertical_tail_bound hy).2]) htθ
      _ < _ := by nlinarith [theta_height_bound hy]
  have hdivy : 2 / y < 12 / 5 :=
    (div_lt_iff₀ hy0).mpr (by linarith [hys.1])
  have hdivsqrt : 2 / Real.sqrt y < 5 / 2 :=
    (div_lt_iff₀ hs0).mpr (by linarith [hys.2.2.1])
  have hterm : (2 / Real.sqrt y) * (thetaFourier y 0 * (1 + verticalTail y)) < 11 / 3 := by
    calc
      _ < (2 / Real.sqrt y) * (22 / 15) := mul_lt_mul_of_pos_left hprod (by positivity)
      _ < _ := by nlinarith
  calc
    _ ≤ (2 / y) * (1 + Real.sqrt y * thetaFourier y 0 * (1 + verticalTail y)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 / y + ((2 / y) * Real.sqrt y) *
        (thetaFourier y 0 * (1 + verticalTail y)) := by ring
    _ = 2 / y + (2 / Real.sqrt y) * (thetaFourier y 0 * (1 + verticalTail y)) := by
      have he : (2 / y) * Real.sqrt y = 2 / Real.sqrt y := by
        field_simp [hy0.ne', hs0.ne']
        nlinarith [Real.sq_sqrt hy0.le]
      rw [he]
    _ < _ := by linarith


private lemma row_even (t y : ℝ) (n : ℤ) : verticalRow t y (-n) = verticalRow t y n := by
  unfold verticalRow
  convert (Equiv.neg ℤ).tsum_eq (fun m : ℤ =>
    Real.exp (-Real.pi * (t / y) * ((m : ℝ) + (n : ℝ) / 2) ^ 2)) using 1
  apply tsum_congr
  intro m
  change Real.exp (-Real.pi * (t / y) *
      ((m : ℝ) + ((-n : ℤ) : ℝ) / 2) ^ 2) =
    Real.exp (-Real.pi * (t / y) *
      (((-m : ℤ) : ℝ) + (n : ℝ) / 2) ^ 2)
  simp only [Int.cast_neg]
  congr 1
  ring

private lemma weighted_row_sum {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    (∑' p : ℤ × ℤ, (p.2 : ℝ) ^ 2 * Real.exp (-Real.pi * t * Q (1 / 2) y p)) =
      2 * Real.exp (-Real.pi * t * (y + 1 / (4 * y))) *
        ∑' k : ℕ, normalizedRow t y k := by
  let g (n : ℤ) := (n : ℝ) ^ 2 * Real.exp (-Real.pi * t * y * (n : ℝ) ^ 2) *
    verticalRow t y n
  have hrow (n : ℤ) : (∑' m : ℤ, (n : ℝ) ^ 2 *
      Real.exp (-Real.pi * t * Q (1 / 2) y (m, n))) = g n := by
    dsimp [g, verticalRow]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    have he : Real.exp (-Real.pi * t * Q (1 / 2) y (m, n)) =
        Real.exp (-Real.pi * t * y * (n : ℝ) ^ 2) *
          Real.exp (-Real.pi * (t / y) * ((m : ℝ) + (n : ℝ) / 2) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [Q]
      field_simp [ht.ne', hy.ne']
      <;> ring
    rw [he]
    ring
  have htotal := (weighted_gaussian_summable ht hy).prod_symm
  have hgs : Summable g := by
    convert htotal.prod using 1
    ext n
    change g n = ∑' m : ℤ, (n : ℝ) ^ 2 *
      Real.exp (-Real.pi * t * Q (1 / 2) y (m, n))
    exact (hrow n).symm
  have hp : Summable (fun k : ℕ => g (k + 1)) := hgs.comp_injective
    (show Function.Injective (fun k : ℕ => (k : ℤ) + 1) from by
      intro a b hab
      exact_mod_cast add_right_cancel hab)
  have heven : (fun k : ℕ => g (-(k + 1))) = (fun k : ℕ => g (k + 1)) := by
    funext k
    dsimp [g]
    rw [row_even]
    simp only [Int.cast_neg, neg_sq]
  have hpos : (∑' k : ℕ, g (k + 1)) =
      Real.exp (-Real.pi * t * (y + 1 / (4 * y))) *
        ∑' k : ℕ, normalizedRow t y k := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [g, normalizedRow]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    have he : Real.exp (-Real.pi * t * y * ((k : ℝ) + 1) ^ 2) =
        Real.exp (-Real.pi * t * (y + 1 / (4 * y))) *
          Real.exp (-Real.pi * t * y * (((k : ℝ) + 1) ^ 2 - 1) +
            Real.pi * t / (4 * y)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [ht.ne', hy.ne']
      <;> ring
    rw [he]
    ring
  calc
    _ = ∑' p : ℤ × ℤ, (p.swap.2 : ℝ) ^ 2 *
        Real.exp (-Real.pi * t * Q (1 / 2) y p.swap) :=
      ((Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ =>
        (p.2 : ℝ) ^ 2 * Real.exp (-Real.pi * t * Q (1 / 2) y p))).symm
    _ = ∑' n : ℤ, ∑' m : ℤ, (n : ℝ) ^ 2 *
        Real.exp (-Real.pi * t * Q (1 / 2) y (m, n)) := by
      simpa only [Prod.swap] using htotal.tsum_prod
    _ = ∑' n : ℤ, g n := tsum_congr hrow
    _ = _ := by
      rw [tsum_of_add_one_of_neg_add_one hp (heven.symm ▸ hp), heven]
      simp_rw [hpos]
      simp only [g, Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero]
      ring

/-- The negative height contribution is bounded by 91/15 of the first-row scale. -/
theorem vertical_negative_bound {t y : ℝ} (ht : 1 ≤ t) (hy : Real.sqrt 3 / 2 ≤ y) :
    verticalNegative t y < (91 / 15) * verticalScale t y := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := (by positivity : 0 < Real.sqrt 3 / 2).trans_le hy
  have h := mul_lt_mul_of_pos_left (normalized_numeric_bound ht hy)
    (show 0 < verticalScale t y by dsimp [verticalScale]; positivity)
  have he := weighted_row_sum ht0 hy0
  rw [verticalNegative, he]
  dsimp [verticalScale] at h ⊢
  convert h using 1 <;> ring


/-- The explicit positive margin in the vertical differential inequality. -/
theorem hexagonal_vertical_differential_bound {t y : ℝ} (ht : 1 ≤ t)
    (hy : Real.sqrt 3 / 2 ≤ y) :
    verticalScale t y * (20 * Real.pi * t / 9 - 91 / 15) <
      deriv (fun b => deriv (fun z => F t (1 / 2) z) b) y +
        (2 / y) * deriv (fun z => F t (1 / 2) z) y := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := (by positivity : 0 < Real.sqrt 3 / 2).trans_le hy
  have hp : 4 / Real.sqrt 3 ≤ Real.pi * t := by
    have hs : 0 < Real.sqrt 3 := by positivity
    have hh : 4 / Real.sqrt 3 < (3 : ℝ) := by
      apply (div_lt_iff₀ hs).mpr
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left ht Real.pi_pos.le, Real.pi_gt_three]
  have hpos := verticalPositive_lower hp hy
  have hneg := vertical_negative_bound ht hy
  rw [vertical_differential_identity ht0 hy0]
  nlinarith

private lemma height_weight_hasDeriv {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    HasDerivAt (fun b => b ^ 2 * deriv (fun z => F t (1 / 2) z) b)
      (y ^ 2 * (deriv (fun b => deriv (fun z => F t (1 / 2) z) b) y +
        (2 / y) * deriv (fun z => F t (1 / 2) z) y)) y := by
  have h2 := hasDerivAt_height_deriv t (1 / 2) ht hy
  have hd := ((hasDerivAt_id y).pow 2).mul h2.differentiableAt.hasDerivAt
  apply hd.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, mul_one]
  field_simp [hy.ne']
  <;> ring

private lemma height_weight_strictMono {t : ℝ} (ht : 1 ≤ t) :
    StrictMonoOn (fun y => y ^ 2 * deriv (fun z => F t (1 / 2) z) y)
      (Set.Ici (Real.sqrt 3 / 2)) := by
  have ht0 : 0 < t := by linarith
  have hc : 0 < Real.sqrt 3 / 2 := by positivity
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro y hy
    exact (height_weight_hasDeriv ht0 (hc.trans_le hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : 0 < y := hc.trans hy
    rw [(height_weight_hasDeriv ht0 hy0).deriv]
    have h := hexagonal_vertical_differential_bound ht hy.le
    have hK : 0 < verticalScale t y := by dsimp [verticalScale]; positivity
    have hm : 0 < 20 * Real.pi * t / 9 - 91 / 15 := by
      nlinarith [mul_le_mul_of_nonneg_left ht Real.pi_pos.le, Real.pi_gt_three]
    exact mul_pos (sq_pos_of_pos hy0) ((mul_pos hK hm).trans h)

private lemma height_derivative_pos_ge_one {t y : ℝ} (ht : 1 ≤ t)
    (hy : Real.sqrt 3 / 2 < y) : 0 < deriv (fun z => F t (1 / 2) z) y := by
  have ht0 : 0 < t := by linarith
  have hc : 0 < Real.sqrt 3 / 2 := by positivity
  have hm := height_weight_strictMono ht
    (show Real.sqrt 3 / 2 ≤ Real.sqrt 3 / 2 from le_rfl) hy.le hy
  dsimp only at hm
  rw [hexagonal_height_stationary ht0, mul_zero] at hm
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (hc.trans hy))).mp hm

/-- The height derivative is positive above the hexagonal height at every temperature. -/
theorem height_derivative_pos {t y : ℝ} (ht : 0 < t)
    (hy : Real.sqrt 3 / 2 < y) : 0 < deriv (fun z => F t (1 / 2) z) y := by
  by_cases ht1 : 1 ≤ t
  · exact height_derivative_pos_ge_one ht1 hy
  · have hy0 : 0 < y := (by positivity : 0 < Real.sqrt 3 / 2).trans hy
    have hinv : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (by linarith)
    have hdinv := hasDerivAt_height t⁻¹ (1 / 2) (inv_pos.mpr ht) hy0
    have hd := hdinv.differentiableAt.hasDerivAt.const_mul t⁻¹
    have he : (fun z => F t (1 / 2) z) =ᶠ[𝓝 y]
        (fun z => t⁻¹ * F t⁻¹ (1 / 2) z) := by
      filter_upwards [eventually_gt_nhds hy0] with z hz
      exact temperature_duality t (1 / 2) ht hz
    rw [(hd.congr_of_eventuallyEq he).deriv]
    exact mul_pos (inv_pos.mpr ht) (height_derivative_pos_ge_one hinv hy)

/-- The hexagonal height uniquely minimizes theta on the vertical half-line. -/
theorem hexagonal_height_minimum {t y : ℝ} (ht : 0 < t)
    (hy : Real.sqrt 3 / 2 ≤ y) :
    F t (1 / 2) (Real.sqrt 3 / 2) ≤ F t (1 / 2) y ∧
      (F t (1 / 2) y = F t (1 / 2) (Real.sqrt 3 / 2) ↔ y = Real.sqrt 3 / 2) := by
  have hc : 0 < Real.sqrt 3 / 2 := by positivity
  have hm : StrictMonoOn (fun y => F t (1 / 2) y) (Set.Ici (Real.sqrt 3 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro y hy
      exact (hasDerivAt_height t (1 / 2) ht (hc.trans_le hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact height_derivative_pos ht hy
  constructor
  · exact hm.monotoneOn (show Real.sqrt 3 / 2 ≤ Real.sqrt 3 / 2 from le_rfl) hy hy
  · constructor
    · intro he
      by_contra hn
      have hlt : Real.sqrt 3 / 2 < y := lt_of_le_of_ne hy (Ne.symm hn)
      have h := hm (show Real.sqrt 3 / 2 ≤ Real.sqrt 3 / 2 from le_rfl) hy hlt
      linarith
    · intro he
      rw [he]

/-- On the entire reduced half-strip the hexagonal point is the unique theta minimizer. -/
theorem reduced_theta_minimum {t x y : ℝ} (ht : 0 < t)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hy : Real.sqrt 3 / 2 ≤ y) :
    F t (1 / 2) (Real.sqrt 3 / 2) ≤ F t x y ∧
      (F t x y = F t (1 / 2) (Real.sqrt 3 / 2) ↔
        x = 1 / 2 ∧ y = Real.sqrt 3 / 2) := by
  have hs := shear_minimum ht hy hx hx'
  have hv := hexagonal_height_minimum ht hy
  constructor
  · exact hv.1.trans hs.1
  · constructor
    · intro he
      have hheight : F t (1 / 2) y = F t (1 / 2) (Real.sqrt 3 / 2) :=
        le_antisymm (by linarith [hs.1]) hv.1
      have hshear : F t x y = F t (1 / 2) y := he.trans hheight.symm
      exact ⟨hs.2.mp hshear, hv.2.mp hheight⟩
    · rintro ⟨rfl, rfl⟩
      rfl


end
end D5.S3.Fourier.PlanarTheta
