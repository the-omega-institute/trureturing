/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Stirling]
   utility: none
   digest: A quantitative factorial remainder retaining every real-floor phase. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! Robbins' public step bound is telescoped and its limit is supplied by
Mathlib's Stirling theorem. The factorial residual is the original arithmetic
object from ActualFactorialRobinHighDerivative. -/

noncomputable section
set_option pp.proofs false
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
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfinite (k : ℕ) :
      Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + k)) ≤
        1 / (12 * n : ℝ) - 1 / (12 * (n + k : ℕ) : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := Stirling.log_stirlingSeq_sdiff_le (n + k)
      have hnk : (0 : ℝ) < (n + k : ℕ) := by exact_mod_cast (show 0 < n + k by omega)
      have ht : (1 : ℝ) / (12 * (n + k : ℕ) * ((n + k : ℕ) + 1)) =
          1 / (12 * (n + k : ℕ) : ℝ) - 1 / (12 * ((n + k : ℕ) + 1)) := by
        field_simp
        ring
      rw [ht] at hstep
      simpa only [Nat.add_succ, Nat.cast_succ] using (by linarith only [ih, hstep] :
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq ((n + k) + 1)) ≤
            1 / (12 * n : ℝ) - 1 / (12 * ((n + k : ℕ) + 1)))
  have hnlim : Tendsto (fun k : ℕ => n + k) atTop atTop :=
    by simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have hloglim : Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq (n + k)))
      atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hnlim)
  have hinvlim : Tendsto (fun k : ℕ => 1 / (12 * (n + k : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hi := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hnlim) : Tendsto
        (fun k : ℕ => ((n + k : ℕ) : ℝ)⁻¹) atTop (𝓝 0))
    simpa only [Function.comp_def, one_div, mul_inv_rev, mul_zero, mul_comm] using hi.const_mul (12 : ℝ)⁻¹
  have hlim := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub hloglim) (tendsto_const_nhds.sub hinvlim)
    (Eventually.of_forall hfinite)
  have he : Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) =
      Real.log (n.factorial : ℝ) -
        ((n : ℝ) * Real.log n - n + Real.log n / 2 + L / 2) := by
    rw [Stirling.log_stirlingSeq_formula,
      Real.log_div hn0.ne' (Real.exp_ne_zero _), Real.log_exp,
      Real.log_mul (by norm_num) hn0.ne', Real.log_sqrt Real.pi_pos.le,
      L, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  constructor
  · have h := Stirling.le_log_factorial_stirling hn.ne'
    dsimp [L]
    linarith
  · simpa only [sub_zero, he] using hlim

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
      nlinarith [mul_nonneg (1 - u) hl]
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
