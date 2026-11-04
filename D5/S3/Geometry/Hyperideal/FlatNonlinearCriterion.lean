/- GID: D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FlatNonlinearCriterion
   mirror-E: none(waiver:exact-flat-nonlinear-criterion)
   anchors: []
   utility: none
   digest: Exact nonlinear flat criterion and sharp opposite-product gap. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FlatNonlinearCriterion

set_option maxHeartbeats 1000000

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

def A (r a d : ℝ) : ℝ := rad r a d

def B (r b c : ℝ) : ℝ := rad r b c

def C (r a b c d : ℝ) : ℝ :=
  r^2 - 1 + (a-d)*(c-b) + 2*(r+1)*Real.sqrt (a*b*c*d)

def S (a b c d : ℝ) : ℝ := Real.sqrt (a*c) + Real.sqrt (b*d)

def J (r a b c d : ℝ) : ℝ :=
  (Real.sqrt (A r a d * B r b c) - C r a b c d) / (r+1)

private theorem rad_pos (r x y : ℝ) (hr : 1 < r) (hx : 1 < x) (hy : 1 < y) :
    0 < rad r x y := by
  have hr2 : 1 ≤ r^2 := by nlinarith [sq_nonneg (r-1)]
  have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
  have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
  have hp : 0 ≤ 2*r*x*y := by positivity
  unfold rad
  linarith

private theorem denominator_pos (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    0 < Real.sqrt (A r a d) * Real.sqrt (B r b c) := by
  exact mul_pos (Real.sqrt_pos.2 (rad_pos r a d hr ha hd))
    (Real.sqrt_pos.2 (rad_pos r b c hr hb hc))

private theorem denominator_sq (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    (Real.sqrt (A r a d) * Real.sqrt (B r b c))^2 = A r a d * B r b c := by
  simp only [A, B]
  rw [mul_pow, Real.sq_sqrt (rad_pos r a d hr ha hd).le,
    Real.sq_sqrt (rad_pos r b c hr hb hc).le]

private theorem sqrt_product (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a*c) * Real.sqrt (b*d) = Real.sqrt (a*b*c*d) := by
  rw [← Real.sqrt_mul (mul_nonneg ha hc)]
  congr 1
  ring

private theorem cauchy_bound (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    C r a b c d ≤ Real.sqrt (A r a d) * Real.sqrt (B r b c) := by
  let U : Fin 3 → ℝ := ![Real.sqrt (r^2-1), a-d, Real.sqrt (2*(r+1)*a*d)]
  let V : Fin 3 → ℝ := ![Real.sqrt (r^2-1), c-b, Real.sqrt (2*(r+1)*b*c)]
  have hr2 : 0 ≤ r^2-1 := by nlinarith [sq_nonneg (r-1)]
  have hp : 0 ≤ 2*(r+1)*a*d := by positivity
  have hq : 0 ≤ 2*(r+1)*b*c := by positivity
  have hprod : 0 ≤ a*b*c*d := by positivity
  have hs : Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) =
      2*(r+1)*Real.sqrt (a*b*c*d) := by
    have hs1 := Real.sq_sqrt hp
    have hs2 := Real.sq_sqrt hq
    have hs3 := Real.sq_sqrt hprod
    have he : (Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c))^2 =
        (2*(r+1)*Real.sqrt (a*b*c*d))^2 := by
      rw [mul_pow, hs1, hs2]
      nlinarith [hs3]
    have hpos1 : 0 ≤ Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) := by positivity
    have hpos2 : 0 ≤ 2*(r+1)*Real.sqrt (a*b*c*d) := by positivity
    nlinarith
  have hU : ∑ i : Fin 3, U i ^ 2 = A r a d := by
    simp [U, A, Fin.sum_univ_succ, Real.sq_sqrt hr2, Real.sq_sqrt hp, rad]
    <;> ring
  have hV : ∑ i : Fin 3, V i ^ 2 = B r b c := by
    simp [V, B, Fin.sum_univ_succ, Real.sq_sqrt hr2, Real.sq_sqrt hq, rad]
    <;> ring
  have hUV : ∑ i : Fin 3, U i * V i = C r a b c d := by
    simp only [U, V, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_one, Fin.val_two,
      Fin.sum_univ_zero, add_zero]
    rw [← pow_two, Real.sq_sqrt hr2, hs]
    dsimp [C]
    ring
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ U V
  simpa only [hU, hV, hUV] using h

/-- The auxiliary correction is nonnegative on the positive length domain. -/
theorem J_nonneg (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    0 ≤ J r a b c d := by
  have hden := denominator_pos r a b c d hr ha hb hc hd
  have h := cauchy_bound r a b c d hr ha hb hc hd
  have hroot : Real.sqrt (A r a d * B r b c) =
      Real.sqrt (A r a d) * Real.sqrt (B r b c) := by
    simp only [A, B]
    rw [Real.sqrt_mul (rad_pos r a d hr ha hd).le]
  dsimp [J]
  rw [hroot]
  exact div_nonneg (sub_nonneg.mpr h) (le_of_lt (by linarith : 0 < r+1))

private theorem numerator_plus_C (r a b o c d : ℝ)
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    numerator r a b o c d + C r a b c d =
      (r+1) * (S a b c d ^ 2 - (r-1)*(o-1)) := by
  have hs := sqrt_product a b c d (by linarith) (by linarith) (by linarith) (by linarith)
  have hac : 0 ≤ a*c := by positivity
  have hbd : 0 ≤ b*d := by positivity
  have hsum_sq : (Real.sqrt (a*c) + Real.sqrt (b*d))^2 =
      a*c + b*d + 2 * (Real.sqrt (a*c) * Real.sqrt (b*d)) := by
    nlinarith [Real.sq_sqrt hac, Real.sq_sqrt hbd]
  dsimp [numerator, C, S]
  rw [hsum_sq, hs]
  ring

private theorem denominator_decomp (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    Real.sqrt (A r a d * B r b c) =
      C r a b c d + (r+1) * J r a b c d := by
  dsimp [J]
  have hrp : r + 1 ≠ 0 := by linarith
  field_simp [hrp]
  ring

/-- The exact flat inequality, including its nonlinear correction term. -/
theorem cosine_le_neg_one_iff (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) :
    cosine r a b o c d ≤ -1 ↔
      (r-1)*(o-1) ≥ S a b c d ^ 2 + J r a b c d := by
  have hden : 0 < Real.sqrt (A r a d) * Real.sqrt (B r b c) :=
    denominator_pos r a b c d hr ha hb hc hd
  have hden' : Real.sqrt (A r a d * B r b c) =
      Real.sqrt (A r a d) * Real.sqrt (B r b c) := by
    simp only [A, B]
    rw [Real.sqrt_mul (rad_pos r a d hr ha hd).le]
  have hsum : numerator r a b o c d +
      Real.sqrt (A r a d) * Real.sqrt (B r b c) =
      (r+1) * (S a b c d ^ 2 - (r-1)*(o-1) + J r a b c d) := by
    calc
      _ = (numerator r a b o c d + C r a b c d) +
          (r+1) * J r a b c d := by
        rw [← hden', denominator_decomp r a b c d hr ha hb hc hd]
        ring
      _ = _ := by
        rw [numerator_plus_C r a b o c d ha hb hc hd]
        ring
  have hquot : cosine r a b o c d ≤ -1 ↔
      numerator r a b o c d + Real.sqrt (A r a d) * Real.sqrt (B r b c) ≤ 0 := by
    rw [cosine, div_div]
    constructor
    · intro h
      have h' := (div_le_iff₀ hden).mp h
      linarith
    · intro h
      apply (div_le_iff₀ hden).mpr
      linarith
  rw [hquot, hsum]
  have hrp : 0 < r+1 := by linarith
  constructor <;> intro h
  · nlinarith
  · nlinarith

private theorem gram_identity (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    A r a d * B r b c - C r a b c d ^ 2 =
      (r^2-1) * ((a-d)-(c-b))^2 +
        (r^2-1) *
          (Real.sqrt (2*(r+1)*a*d) - Real.sqrt (2*(r+1)*b*c))^2 +
        ((a-d) * Real.sqrt (2*(r+1)*b*c) -
          Real.sqrt (2*(r+1)*a*d) * (c-b))^2 := by
  have hR : 0 ≤ r^2 - 1 := by nlinarith [sq_nonneg (r-1)]
  have hp : 0 ≤ 2*(r+1)*a*d := by positivity
  have hq : 0 ≤ 2*(r+1)*b*c := by positivity
  have hprod : 0 ≤ a*b*c*d := by positivity
  have hA : A r a d = (r^2-1) + (a-d)^2 +
      Real.sqrt (2*(r+1)*a*d)^2 := by
    dsimp [A]
    rw [Real.sq_sqrt hp]
    unfold rad
    ring
  have hB : B r b c = (r^2-1) + (c-b)^2 +
      Real.sqrt (2*(r+1)*b*c)^2 := by
    dsimp [B]
    rw [Real.sq_sqrt hq]
    unfold rad
    ring
  have hpq : Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) =
      2*(r+1)*Real.sqrt (a*b*c*d) := by
    exact (by
      have hs1 := Real.sq_sqrt hp
      have hs2 := Real.sq_sqrt hq
      have hs3 := Real.sq_sqrt hprod
      have he : (Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c))^2 =
          (2*(r+1)*Real.sqrt (a*b*c*d))^2 := by
        rw [mul_pow, hs1, hs2]
        nlinarith [hs3]
      have hpos1 : 0 ≤ Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) := by positivity
      have hpos2 : 0 ≤ 2*(r+1)*Real.sqrt (a*b*c*d) := by positivity
      nlinarith)
  have hC : C r a b c d = (r^2-1) + (a-d)*(c-b) +
      Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) := by
    dsimp [C]
    rw [hpq]
  rw [hA, hB, hC]
  ring

/-- Equality in the nonlinear correction is exactly the opposite-pair symmetry. -/
theorem J_eq_zero_iff (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    J r a b c d = 0 ↔ a = c ∧ b = d := by
  constructor
  · intro hJ
    have hpos : 0 < Real.sqrt (A r a d) * Real.sqrt (B r b c) :=
      denominator_pos r a b c d hr ha hb hc hd
    have hAB : 0 ≤ A r a d * B r b c := by
      exact (mul_pos (rad_pos r a d hr ha hd) (rad_pos r b c hr hb hc)).le
    have hrp : r + 1 ≠ 0 := by linarith
    have hEq : Real.sqrt (A r a d * B r b c) = C r a b c d := by
      dsimp [J] at hJ
      field_simp [hrp] at hJ
      have hJ' : Real.sqrt (A r a d * B r b c) - C r a b c d = 0 := by
        simpa using hJ
      exact sub_eq_zero.mp hJ'
    have hsq : A r a d * B r b c = C r a b c d ^ 2 := by
      rw [← Real.sq_sqrt hAB, hEq]
    have hgram := gram_identity r a b c d hr ha hb hc hd
    have hsum :
        (r^2-1) * ((a-d)-(c-b))^2 +
          (r^2-1) *
            (Real.sqrt (2*(r+1)*a*d) - Real.sqrt (2*(r+1)*b*c))^2 +
          ((a-d) * Real.sqrt (2*(r+1)*b*c) -
            Real.sqrt (2*(r+1)*a*d) * (c-b))^2 = 0 := by
      nlinarith [hgram, hsq]
    have hRpos : 0 < r^2 - 1 := by nlinarith [hr]
    have hterm1 : 0 ≤ (r^2-1) * ((a-d)-(c-b))^2 :=
      mul_nonneg hRpos.le (sq_nonneg _)
    have hterm2 : 0 ≤ (r^2-1) *
        (Real.sqrt (2*(r+1)*a*d) - Real.sqrt (2*(r+1)*b*c))^2 :=
      mul_nonneg hRpos.le (sq_nonneg _)
    have hterm3 : 0 ≤ ((a-d) * Real.sqrt (2*(r+1)*b*c) -
        Real.sqrt (2*(r+1)*a*d) * (c-b))^2 := sq_nonneg _
    have hzero1 : (r^2-1) * ((a-d)-(c-b))^2 = 0 := by
      have hle : (r^2-1) * ((a-d)-(c-b))^2 ≤ 0 := by
        linarith [hsum, hterm2, hterm3]
      exact le_antisymm hle hterm1
    have hzero2 : (r^2-1) *
        (Real.sqrt (2*(r+1)*a*d) - Real.sqrt (2*(r+1)*b*c))^2 = 0 := by
      have hle : (r^2-1) *
          (Real.sqrt (2*(r+1)*a*d) - Real.sqrt (2*(r+1)*b*c))^2 ≤ 0 := by
        linarith [hsum, hterm1, hterm3]
      exact le_antisymm hle hterm2
    have hxy : ((a-d)-(c-b))^2 = 0 := by
      rcases mul_eq_zero.mp hzero1 with h | h
      · exfalso; nlinarith
      · exact h
    have hpq : (Real.sqrt (2*(r+1)*a*d) -
        Real.sqrt (2*(r+1)*b*c))^2 = 0 := by
      rcases mul_eq_zero.mp hzero2 with h | h
      · exfalso; nlinarith
      · exact h
    have hxy' : a-d = c-b := by nlinarith only [hxy]
    have hpq' : Real.sqrt (2*(r+1)*a*d) =
        Real.sqrt (2*(r+1)*b*c) := by nlinarith only [hpq]
    have hadbc : a*d = b*c := by
      have hpa := Real.sq_sqrt (show 0 ≤ 2*(r+1)*a*d by positivity)
      have hpb := Real.sq_sqrt (show 0 ≤ 2*(r+1)*b*c by positivity)
      have hsquare := congrArg (fun x : ℝ => x^2) hpq'
      rw [hpa, hpb] at hsquare
      have hcoef : (2 * (r+1)) ≠ 0 := by positivity
      have hsquare' : (2 * (r+1)) * (a*d) =
          (2 * (r+1)) * (b*c) := by
        simpa [mul_assoc] using hsquare
      exact mul_left_cancel₀ hcoef hsquare'
    have habsum : a + b = c + d := by linarith
    have hfac : (a-c) * (a+b) = 0 := by
      calc
        (a-c) * (a+b) = a * (a+b) - c * (a+b) := by ring
        _ = a * (c+d) - c * (a+b) := by rw [habsum]
        _ = a*d - b*c := by ring
        _ = 0 := sub_eq_zero.mpr hadbc
    have hac : a = c := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exfalso; nlinarith [ha, hb]
    have hbd : b = d := by linarith [habsum, hac]
    exact ⟨hac, hbd⟩
  · rintro ⟨rfl, rfl⟩
    have hrab : 0 < rad r a b := rad_pos r a b hr ha hb
    have hab : 0 < a*b := mul_pos (by linarith) (by linarith)
    have hrad : rad r b a = rad r a b := by unfold rad; ring
    have hroot : Real.sqrt (rad r a b * rad r a b) = rad r a b := by
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hrab]
    have hprod : Real.sqrt (a*b*a*b) = a*b := by
      rw [show a*b*a*b = (a*b)^2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos hab]
    dsimp [J, A, B, C]
    rw [hrad, hroot, hprod]
    have hrp : r + 1 ≠ 0 := by linarith
    field_simp [hrp]
    unfold rad
    ring

/-- In the symmetric transverse case the nonlinear correction vanishes. -/
theorem symmetric_cosine_le_neg_one_iff (r a b o : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o) :
    cosine r a b o a b ≤ -1 ↔ (r-1)*(o-1) ≥ (a+b)^2 := by
  have hcrit := cosine_le_neg_one_iff r a b o a b hr ha hb ho ha hb
  have hJ := J_eq_zero_iff r a b a b hr ha hb ha hb
  have hsa : Real.sqrt (a*a) = a := by
    rw [show a*a = a^2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
  have hsb : Real.sqrt (b*b) = b := by
    rw [show b*b = b^2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
  have hJ0 : J r a b a b = 0 := hJ.mpr ⟨rfl, rfl⟩
  rw [hcrit, hJ0]
  dsimp [S]
  rw [hsa, hsb]
  simp

#print axioms J_eq_zero_iff
#print axioms symmetric_cosine_le_neg_one_iff

#print axioms J_nonneg
#print axioms cosine_le_neg_one_iff

end D5.S3.Geometry.Hyperideal.FlatNonlinearCriterion
