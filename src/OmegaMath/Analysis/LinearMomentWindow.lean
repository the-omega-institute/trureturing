-- Adapted from the exponential-majorant argument in:
-- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/OneSidedCriterion.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GRewrite
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
Omega original.

Signed factorial moments and exponential envelopes give a uniformly good scale
in a fixed linear window.
-/

open Filter Nat Real Set MeasureTheory Topology

namespace Omega.Analysis

private lemma real_laplace_pow {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∫ v : ℝ in Ioi 0, v ^ k * exp (-a * v) = (k.factorial : ℝ) / a ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((k + 1 : ℕ) : ℝ)) (by positivity) ha
  have hk : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by norm_num
  rw [hk, Real.rpow_natCast, Real.rpow_natCast] at h
  simpa [Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial, neg_mul,
    one_div, inv_pow, div_eq_mul_inv, mul_comm] using h

/-- Exponential envelopes and signed factorial-moment bounds suffice for a good
second scale in a linear window. No transform, meromorphic continuation, or
residue hypothesis is required. -/
theorem exists_linear_window_of_signed_moments {E E' : ℝ → ℝ}
    (moments : ∃ R ∈ Ioo (3 : ℝ) 4,
      (∀ᶠ t in atTop, (∀ v ≥ 0, |E v| ≤ t * v.exp) ∧ ∀ k : ℕ,
        IntegrableOn (fun v ↦ v ^ k * exp (-3 * v) * E v) (Ioi 0) ∧
        |∫ v in Ioi 0, v ^ k * exp (-3 * v) * E v| ≤ k ! * t / R ^ k) ∧
      (∀ᶠ t in atTop, (∀ v ≥ 0, |E' v| ≤ t * v.exp) ∧ ∀ k : ℕ,
        IntegrableOn (fun v ↦ v ^ k * exp (-3 * v) * E' v) (Ioi 0) ∧
        |∫ v in Ioi 0, v ^ k * exp (-3 * v) * E' v| ≤ k ! * t / R ^ k)) :
    ∃ C : ℝ, 1 < C ∧ ∀ᶠ t in atTop,
      ∀ X ∈ Icc 0 t.exp, ∃ u ∈ Icc t (C * t), E u - X * E' u ≤ (-t).exp := by
  obtain ⟨R, ⟨p, q⟩, c, d⟩ := moments
  have hd : 0 < R.log - log 3 := sub_pos.2 (log_lt_log (by norm_num) p)
  have hd1 : R.log - log 3 ≤ 1 := by
    rw [← log_div (by linarith : R ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    have := log_le_sub_one_of_pos (by linarith : 0 < R / 3)
    linarith
  let C := 99 / (R.log - log 3)
  have hC : 99 ≤ C := (le_div_iff₀ hd).2 (by nlinarith)
  have hCpos : 0 < C := by linarith
  have hCd : C * (R.log - log 3) = 99 := div_mul_cancel₀ _ hd.ne'
  refine ⟨C, by linarith, ?_⟩
  simp_rw [IntegrableOn, abs_le, forall_and] at c d
  filter_upwards [c, d, mem_atTop (9 : ℝ)] with t ⟨c, _, a⟩ ⟨d, _, b⟩ ht X ⟨_, _⟩
  have htpos : 0 < t := by linarith
  let k := ⌈C * t / 9⌉₊
  have hCt : C * t * (R.log - log 3) = 99 * t := by
    calc _ = (C * (R.log - log 3)) * t := by ring
         _ = _ := by rw [hCd]
  have hk : -1 ≤ C * t / 9 - (k : ℝ) ∧ C * t / 9 - (k : ℝ) ≤ 1 :=
    abs_le.1 (abs_sub_ceil_le (by positivity : 0 ≤ C * t / 9))
  have hCtlarge : 99 * t ≤ C * t := mul_le_mul_of_nonneg_right hC htpos.le
  have hkδ : 11 * t ≤ (k : ℝ) * (R.log - log 3) := by
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil (C * t / 9)) hd.le
    change C * t / 9 * (R.log - log 3) ≤ (k : ℝ) * (R.log - log 3) at this
    nlinarith
  have hlog3 : log 3 ≤ 11 / 10 := by linarith [log_three_lt_d9]
  have hklog : (k : ℝ) * log 3 ≤ (k : ℝ) * (11 / 10) :=
    mul_le_mul_of_nonneg_left hlog3 (by positivity)
  obtain ⟨w, I, K : t + t * X + 1 ≤ t.exp * t.exp⟩ := three_pos.trans p,
    fun (a : ℝ) (ha : 0 < a) ↦ real_laplace_pow ha k, by nlinarith [t.add_one_le_exp]
  have J R o := Integrable.of_integral_ne_zero ((I R o).trans_ne (by simp; grind))
  by_contra! N
  have : 0 ≤ ∫ v in Ioi 0, v ^ k * ((-R * v).exp * (7 * t).exp + (-1 * v).exp *
    (2 * t - C * t).exp + (-3 * v).exp * (E v - _ * X - (-t).exp)) := setIntegral_nonneg
    (by simp) fun v (l : 0 < v) ↦ mul_nonneg (by bound) (by_cases (by bound [N v ·]) fun x ↦ ?_)
  · simp (disch := first | fun_prop (disch := simp [w]) | simp [*]) [mul_add, mul_sub, ← mul_assoc,
      integral_add, integral_sub, I, -neg_mul] at this
    grw [a.2, ← b.1, (by ring : _ - _ * X = k ! * (t + t * X) / R ^ k), lt_add_one (t + _), K,
      add_sub, sub_pos] at this
    apply this.not_ge ((add_le_add_three ..).trans_eq (add_thirds _)) <;>
      simp (disch := positivity) [← log_le_log_iff] <;> nlinarith [log_three_lt_d9]
  grw [← neg_le_iff_add_nonneg, ← c.1, d.2, (by grind : -t ≤ v), (by ring : -_ = (-3 * v).exp *
    v.exp * (t + t * X + 1)), K, ← max_le_add_of_nonneg] <;> simp [← Real.exp_add, exp_nonneg, l.le]
  contrapose! x; use ?_ <;> nlinarith

end Omega.Analysis
