/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Stirling]
   utility: none
   digest: Floor-uniform harmonic and factorial remainders for the literal factorial compensation. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.Basic
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
The public finite smoothing and slope contract belong to Basic. The harmonic
bracket is reused from RobinRationalBasis; the factorial estimate uses Mathlib
Stirling. No private supplier declaration or proof is used. The real floor
phase is retained throughout.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

/-- The exact constant identified by the factorial and harmonic cancellations. -/
def ell : ℝ := alpha + h1 / 2

/-- A compensated primitive of the actual harmonic error. -/
def harmonicPrimitive (x : ℝ) : ℝ := x * epsilon x + Int.fract x - 1 / 2

lemma J_tail_from_slope {x : ℝ} (hx : 1 ≤ x) :
    2 * J x = (Real.log x) ^ 2 - gamma ^ 2 + alpha +
      2 * Real.log x * epsilon x + 2 * T_epsilon x := by
  have hs := (compensation.2.2.2.2.2.1 x hx).1
  dsimp [slope, epsilon] at hs ⊢
  nlinarith only [hs]

lemma G_tail_decomposition {x : ℝ} (hx : 1 ≤ x) :
    G x = alpha + (1 + gamma) * Int.fract x - eta x +
      x * (1 + gamma + Real.log x) * epsilon x + 2 * x * T_epsilon x := by
  have he := ActualFactorialRobinHighDerivative.result.1 x
  have hj := J_tail_from_slope hx
  have hf : Int.fract x = x - (⌊x⌋₊ : ℝ) := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor (by linarith : 0 ≤ x)]
  rw [G, finite_smoothing hx, h1]
  dsimp [epsilon]
  rw [hf]
  nlinarith only [hj, he]

lemma H_eq_harmonic (x : ℝ) : H x = (harmonic ⌊x⌋₊ : ℝ) := by
  simp only [H, prefixSum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp

/-- Elementary real-floor bounds, including the entire first cell. -/
lemma harmonicPrimitive_bound {x : ℝ} (hx : 1 ≤ x) :
    |harmonicPrimitive x| ≤ 4 / x := by
  let n : ℕ := ⌊x⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff x).mpr hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx0 : 0 < x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hratio : 0 < x / n := div_pos hx0 hn0
  have hlogu := Real.log_le_sub_one_of_pos hratio
  have hlogl := Real.one_sub_inv_le_log_of_pos hratio
  rw [Real.log_div hx0.ne' hn0.ne'] at hlogu hlogl
  have hb := GoldenResource.RobinRationalBasis.eulerMascheroni_remainder_bounds n hn
  have hfrac : Int.fract x = x - (n : ℝ) := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hx0.le]
  rw [harmonicPrimitive, epsilon, H_eq_harmonic, hfrac, abs_le]
  change -(4 / x) ≤ x * ((harmonic n : ℝ) - Real.log x - gamma) +
      (x - (n : ℝ)) - 1 / 2 ∧
    x * ((harmonic n : ℝ) - Real.log x - gamma) + (x - (n : ℝ)) - 1 / 2 ≤ 4 / x
  have hmul_u := mul_le_mul_of_nonneg_left hlogu hx0.le
  have hmul_l := mul_le_mul_of_nonneg_left hlogl hx0.le
  have hmul_hi := mul_le_mul_of_nonneg_left hb.2.le hx0.le
  have hmul_lo := mul_le_mul_of_nonneg_left hb.1.le hx0.le
  constructor <;> dsimp [gamma] at *
  · field_simp at hmul_l hmul_u hmul_hi hmul_lo ⊢
    nlinarith [sq_nonneg (x - n)]
  · field_simp at hmul_l hmul_u hmul_hi hmul_lo ⊢
    nlinarith [sq_nonneg (x - n)]

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
