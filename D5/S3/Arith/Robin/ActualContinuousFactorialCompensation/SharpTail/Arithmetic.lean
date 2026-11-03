/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Stirling]
   utility: none
   digest: Real-floor harmonic remainders for the literal factorial compensation. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.Basic
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
The public finite smoothing and slope contract belong to Basic. The harmonic
bracket is reused from RobinRationalBasis; the factorial estimate uses Mathlib
Stirling. The original Basic harmonic supplier is reused directly. The real floor
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
  have hH : H x = Real.log x + gamma + epsilon x := by simp [epsilon]
  rw [hj, hH, show eta x = Real.log (⌊x⌋₊.factorial : ℝ) -
    (x * Real.log x - x) from he, hf]
  ring

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
  let d : ℝ := (harmonic n : ℝ) - Real.log n - gamma
  let l : ℝ := Real.log x - Real.log n
  let u : ℝ := x - n
  have hu : 0 ≤ u ∧ u ≤ 1 := ⟨sub_nonneg.mpr hnx, by dsimp [u]; linarith⟩
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (u - 1)]
  have hd : 1 / (2 * ((n : ℝ) + 1)) ≤ d ∧ d ≤ 1 / (2 * n) :=
    ⟨hb.1.le, hb.2.le⟩
  have hdl : -(1 / n : ℝ) ≤ x * d - 1 / 2 := by
    calc
      -(1 / n : ℝ) ≤ (n : ℝ) / (2 * ((n : ℝ) + 1)) - 1 / 2 := by
        field_simp
        nlinarith
      _ ≤ x * d - 1 / 2 := by
        simpa only [mul_one_div] using
          (sub_le_sub_right (mul_le_mul hnx hd.1 (by positivity) hx0.le) (1 / 2))
  have hdu : x * d - 1 / 2 ≤ 1 / n := by
    calc
      _ ≤ x * (1 / (2 * n)) - 1 / 2 := by gcongr; exact hd.2
      _ ≤ 1 / n := by
        field_simp
        nlinarith
  have hll : 0 ≤ x * l - u := by
    have h := mul_le_mul_of_nonneg_left hlogl hx0.le
    dsimp [l, u]
    field_simp at h
    linarith
  have hlu : x * l - u ≤ 1 / n := by
    have h := mul_le_mul_of_nonneg_left hlogu hx0.le
    dsimp [l, u] at *
    apply (le_div_iff₀ hn0).mpr
    have h' := mul_le_mul_of_nonneg_left h hn0.le
    field_simp at h'
    nlinarith only [mul_le_mul_of_nonneg_left h' hx0.le, hu2]
  have he : harmonicPrimitive x = (x * d - 1 / 2) - (x * l - u) := by
    rw [harmonicPrimitive, epsilon, H_harmonic, hfrac]
    dsimp [d, l, u, n]
    ring
  have hf : |harmonicPrimitive x| ≤ 2 / n := by
    rw [he, abs_le]
    simp only [div_eq_mul_inv] at hdl hdu hlu ⊢
    constructor <;> linarith
  refine hf.trans ?_
  apply (div_le_div_iff₀ hn0 hx0).mpr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith


end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
