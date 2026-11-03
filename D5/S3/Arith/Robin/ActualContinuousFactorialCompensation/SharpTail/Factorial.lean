/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Stirling]
   utility: none
   digest: A quantitative factorial remainder retaining every real-floor phase. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.Basic
import D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! The logarithmic factorial envelope is supplied by the original Grid owner;
its proof telescopes Mathlib's Robbins step to the Stirling limit. The
factorial residual is the original arithmetic object from
ActualFactorialRobinHighDerivative. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

lemma log_factorial_remainder {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log (n.factorial : ℝ) -
      ((n : ℝ) * Real.log n - n + Real.log n / 2 + L / 2) ∧
    Real.log (n.factorial : ℝ) -
      ((n : ℝ) * Real.log n - n + Real.log n / 2 + L / 2) ≤ 1 / (12 * n) := by
  have hup := D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound.log_factorial_upper_bound n hn
  have hlow := Stirling.le_log_factorial_stirling (n := n) hn.ne'
  constructor
  · dsimp [L]
    linarith
  · dsimp [L] at hup ⊢
    linarith

/-- A first-order factorial expansion uniform in the complete floor cell. -/
lemma eta_phase_bound {x : ℝ} (hx : 1 ≤ x) :
    |eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2)| ≤ 4 / x := by
  let n : ℕ := ⌊x⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff x).mpr hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx0 : 0 < x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  let u : ℝ := x - n
  let l : ℝ := Real.log x - Real.log n
  have hu : 0 ≤ u ∧ u ≤ 1 := ⟨sub_nonneg.mpr hnx, by dsimp [u]; linarith⟩
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (u - 1)]
  have hl : 0 ≤ l := sub_nonneg.mpr (Real.log_le_log hn0 hnx)
  have hlo := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hn0)
  have hhi := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
  rw [Real.log_div hx0.ne' hn0.ne'] at hlo hhi
  have he := ActualFactorialRobinHighDerivative.result.1 x
  have hf : Int.fract x = u := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hx0.le]
  let s : ℝ := Real.log (n.factorial : ℝ) -
    ((n : ℝ) * Real.log n - n + Real.log n / 2 + L / 2)
  have hs : 0 ≤ s ∧ s ≤ 1 / (12 * n) := log_factorial_remainder (by omega)
  have hid : eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2) =
      s - (((n : ℝ) + 1 / 2) * l - u) := by
    rw [show eta x = Real.log (n.factorial : ℝ) - (x * Real.log x - x) from he, hf]
    dsimp [s, l, u]
    ring
  have hlog : l ≤ 1 / n := by
    dsimp [l]
    calc
      _ ≤ x / n - 1 := hhi
      _ ≤ 1 / n := by field_simp; linarith
  have hlow : -(1 / n : ℝ) ≤ ((n : ℝ) + 1 / 2) * l - u := by
    have h := mul_le_mul_of_nonneg_left hlo hx0.le
    have huL : u * l ≤ 1 / n := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hl]
    dsimp [l, u] at *
    field_simp at h
    nlinarith only [h, huL, hl]
  have hhigh : ((n : ℝ) + 1 / 2) * l - u ≤ 1 / n := by
    have h := mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ (n : ℝ) + 1 / 2)
    dsimp [l, u] at *
    apply (le_div_iff₀ hn0).mpr
    field_simp at h
    nlinarith
  have hsmall : |eta x - ((1 / 2 - Int.fract x) * Real.log x + L / 2)| ≤ 2 / n := by
    rw [hid, abs_le]
    have hs' : s ≤ 1 / n := hs.2.trans (by
      apply one_div_le_one_div_of_le hn0
      nlinarith)
    simp only [div_eq_mul_inv] at hlow hhigh hs' ⊢
    constructor <;> linarith
  refine hsmall.trans ((div_le_div_iff₀ hn0 hx0).mpr ?_)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
