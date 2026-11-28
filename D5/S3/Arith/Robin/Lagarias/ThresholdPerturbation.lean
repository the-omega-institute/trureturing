/- GID: D5/S3/Arith/Robin/Lagarias/ThresholdPerturbation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Lagarias/ThresholdPerturbation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The Lagarias threshold has an exact leading perturbation of the Robin threshold. -/

import OmegaBuild.Commands
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib
import OmegaBuild.Commands

compile_only_with_mathlib

/-! The harmonic threshold as a vanishing perturbation of the Robin threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation

private abbrev E : ℝ := Real.exp Real.eulerMascheroniConstant

def threshold (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

def gap (n : ℕ) : ℝ :=
  threshold n / n - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))

private lemma gap_bounds (n : ℕ) (hn : 1 < Real.log (n : ℝ)) :
    let x := Real.log (n : ℝ)
    let a := (harmonic n : ℝ) - x
    E * a / (1 + a / x) ≤ x * gap n ∧
    x * gap n ≤ E * a + (1 + E) * ((x ^ 2 + x) / n) := by
  let N : ℝ := n
  let x := Real.log N
  let H : ℝ := harmonic n
  let a := H - x
  let b := Real.exp H / N - E
  let q := Real.log H - Real.log x
  have hn0 : n ≠ 0 := by
    intro he
    simp [he] at hn
  have hN : 0 < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hx : 0 < x := lt_trans zero_lt_one hn
  have hgamma : Real.eulerMascheroniConstant < a := by
    simpa [a, H, x, N, Real.eulerMascheroniSeq', hn0] using
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have ha : 0 < a := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hH : 0 < H := by dsimp [a] at ha; linarith
  have hH1 : 1 < H := by dsimp [a] at ha; linarith
  have hHup : H ≤ x + 1 := by
    have hh := harmonic_le_one_add_log n
    change H ≤ 1 + x at hh
    linarith
  have hElower : E * N ≤ Real.exp H := by
    calc
      E * N = Real.exp (Real.eulerMascheroniConstant + x) := by
        rw [Real.exp_add, Real.exp_log hN]
      _ ≤ Real.exp H := Real.exp_le_exp.mpr (by dsimp [a] at hgamma; linarith)
  have hEupper : Real.exp H ≤ E * (N + 1) := by
    have hh := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    change H - Real.log (N + 1) < Real.eulerMascheroniConstant at hh
    calc
      Real.exp H ≤ Real.exp (Real.eulerMascheroniConstant + Real.log (N + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = E * (N + 1) := by rw [Real.exp_add, Real.exp_log (by positivity)]
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith [(le_div_iff₀ hN).mpr hElower]
  have hbup : b ≤ E / N := by
    dsimp [b]
    have hh := div_le_div_of_nonneg_right hEupper hN.le
    have heq : E * (N + 1) / N = E + E / N := by field_simp; ring
    linarith
  have hlogH : 0 ≤ Real.log H := (Real.log_pos hH1).le
  have hlogHup : Real.log H ≤ x + 1 :=
    (Real.log_le_sub_one_of_pos hH).trans (by linarith)
  have hqlo : 1 - x / H ≤ q := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hH hx)
    simpa [q, Real.log_div hH.ne' hx.ne', inv_div] using hh
  have hqup : q ≤ H / x - 1 := by
    simpa [q, Real.log_div hH.ne' hx.ne'] using
      Real.log_le_sub_one_of_pos (div_pos hH hx)
  have hid : x * gap n = x * H / N + x * b * Real.log H + E * x * q := by
    dsimp [gap, threshold, b, q, x, H, N, E]
    field_simp [hN.ne']
    ring
  have hloeq : E * a / (1 + a / x) = E * x * (1 - x / H) := by
    have hden : 1 + a / x = H / x := by
      dsimp [a]
      field_simp [hx.ne']
      ring
    rw [hden]
    dsimp [a]
    field_simp [hx.ne', hH.ne']
    ring
  have hulo : E * x * q ≤ E * a := by
    have hh := mul_le_mul_of_nonneg_left hqup
      (mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hx).le
    have heq : E * x * (H / x - 1) = E * a := by
      dsimp [a]
      field_simp [hx.ne']
      ring
    rwa [heq] at hh
  have herr : x * H / N + x * b * Real.log H ≤
      (1 + E) * ((x ^ 2 + x) / N) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHup hx.le) hN.le
    have hh' := mul_le_mul_of_nonneg_left
      (mul_le_mul hbup hlogHup hlogH (by positivity : 0 ≤ E / N)) hx.le
    simp only [div_eq_mul_inv] at hh hh' ⊢
    nlinarith only [hh, hh']
  change E * a / (1 + a / x) ≤ x * gap n ∧
    x * gap n ≤ E * a + (1 + E) * ((x ^ 2 + x) / N)
  rw [hid]
  constructor
  · rw [hloeq]
    have hh := mul_le_mul_of_nonneg_left hqlo
      (mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hx).le
    have hr : 0 ≤ x * H / N := by positivity
    have hr' : 0 ≤ x * b * Real.log H := by positivity
    linarith
  · linarith

/-- The exact leading coefficient of the difference between the harmonic and
Robin thresholds, after division by the integer. -/
theorem threshold_asymptotic :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * gap n) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * Real.eulerMascheroniConstant)) := by
  let x (n : ℕ) := Real.log (n : ℝ)
  let a (n : ℕ) := (harmonic n : ℝ) - x n
  have hx : Tendsto x atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto a atTop (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hax : Tendsto (fun n => a n / x n) atTop (𝓝 0) := ha.div_atTop hx
  have hlo : Tendsto (fun n => E * a n / (1 + a n / x n)) atTop
      (𝓝 (E * Real.eulerMascheroniConstant)) := by
    have hd : Tendsto (fun n => 1 + a n / x n) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add hax
    simpa using (ha.const_mul E).div hd one_ne_zero
  have hp (k : ℕ) : Tendsto (fun n : ℕ => x n ^ k / (n : ℝ)) atTop (𝓝 0) := by
    simpa [x] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => (x n ^ 2 + x n) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [add_div] using (hp 2).add (by simpa using hp 1)
  have hup : Tendsto (fun n : ℕ => E * a n + (1 + E) *
      ((x n ^ 2 + x n) / (n : ℝ))) atTop (𝓝 (E * Real.eulerMascheroniConstant)) := by
    simpa using (ha.const_mul E).add (herr.const_mul (1 + E))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [hx.eventually_gt_atTop 1] with n hn
    exact (gap_bounds n hn).1
  · filter_upwards [hx.eventually_gt_atTop 1] with n hn
    exact (gap_bounds n hn).2

end D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation
