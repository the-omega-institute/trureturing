/- GID: D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/ForbergExponentialFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forberg's exponential quotient has the shifted quarter-square floor for every positive integer. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor

private lemma bounds {r : ℝ} (hr : 2 ≤ r) :
    (r - 1)^2 / 4 ≤ r / (Real.exp (4 / r) - 1) ∧
    r / (Real.exp (4 / r) - 1) < r^2 / 4 - r / 2 + 1 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hd : 0 < Real.exp (4 / r) - 1 := by
    apply sub_pos.mpr
    exact Real.one_lt_exp_iff.mpr (by positivity)
  let q : ℝ := (1 + 1 / r) / (1 - 1 / r)
  have hu : 1 / r < 1 := (div_lt_one hr0).mpr (by linarith)
  have h1u : 0 < 1 - 1 / r := sub_pos.mpr hu
  have hqpos : 0 < q := by dsimp [q]; exact div_pos (by positivity) h1u
  have hlog := Real.sum_range_le_log_div (x := 1 / r) (by positivity) hu 1
  norm_num at hlog
  have hlog' : 4 / r ≤ Real.log q + Real.log q := by
    dsimp [q]
    simp only [div_eq_mul_inv, one_mul] at hlog ⊢
    linarith only [hlog]
  have he := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_add, Real.exp_log hqpos] at he
  have hq : q = (r + 1) / (r - 1) := by
    dsimp [q]
    field_simp [hr0.ne', hr1.ne', h1u.ne']
    <;> ring
  have he2 : Real.exp (4 / r) ≤ ((r + 1) / (r - 1))^2 := by
    simpa [hq, pow_two] using he
  rw [div_pow] at he2
  have he' := (le_div_iff₀ (sq_pos_of_pos hr1)).mp he2
  have hlo : (r - 1)^2 / 4 ≤ r / (Real.exp (4 / r) - 1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [he']
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4 / r by positivity)
  have hmul := mul_le_mul_of_nonneg_right hquad (sq_nonneg r)
  have hid : (1 + 4 / r + (4 / r)^2 / 2) * r^2 = r^2 + 4 * r + 8 := by
    field_simp [hr0.ne']
    <;> ring
  rw [hid] at hmul
  have hQ : 0 < r^2 / 4 - r / 2 + 1 := by nlinarith [sq_nonneg (r - 1)]
  have hdquad : 4 * r + 8 ≤ (Real.exp (4 / r) - 1) * r^2 := by nlinarith only [hmul]
  have hp := mul_le_mul_of_nonneg_left hdquad hQ.le
  have hhi : r / (Real.exp (4 / r) - 1) < r^2 / 4 - r / 2 + 1 := by
    apply (div_lt_iff₀ hd).mpr
    by_contra h
    have hh : (r^2 / 4 - r / 2 + 1) * (Real.exp (4 / r) - 1) ≤ r := le_of_not_gt h
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg r)
    nlinarith only [hp, hh']
  exact ⟨hlo, hhi⟩

theorem result (n : ℕ) (hn : 1 ≤ n) :
    (⌊(n : ℝ) / (Real.exp (4 / (n : ℝ)) - 1)⌋ : ℤ) =
      ⌊(((n : ℝ) - 1)^2 / 4)⌋ := by
  by_cases h1 : n = 1
  · subst n
    have he := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
    norm_num at he
    have hd : 0 < Real.exp 4 - 1 := by linarith
    have hf : (⌊(1 : ℝ) / (Real.exp 4 - 1)⌋ : ℤ) = 0 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · simpa using (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hd.le)
      · simpa using ((div_lt_one hd).mpr (by linarith : (1 : ℝ) < Real.exp 4 - 1))
    simpa using hf
  have hn2 : 2 ≤ n := by omega
  have hb := bounds (r := (n : ℝ)) (by exact_mod_cast hn2)
  let k : ℕ := n / 2
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm
  · have hnk : n = 2 * k := by dsimp [k]; omega
    have hnr : (n : ℝ) = 2 * (k : ℝ) := by exact_mod_cast hnk
    rw [hnr] at hb
    let z : ℤ := (k : ℤ) * ((k : ℤ) - 1)
    have hz : (z : ℝ) = (k : ℝ)^2 - (k : ℝ) := by
      dsimp [z]
      push_cast
      ring
    have hf : (⌊(n : ℝ) / (Real.exp (4 / (n : ℝ)) - 1)⌋ : ℤ) = z := by
      rw [hnr]
      apply Int.floor_eq_iff.mpr
      constructor <;> rw [hz] <;> nlinarith only [hb.1, hb.2]
    have hg : (⌊(((n : ℝ) - 1)^2 / 4)⌋ : ℤ) = z := by
      rw [hnr]
      apply Int.floor_eq_iff.mpr
      constructor <;> rw [hz] <;> nlinarith
    exact hf.trans hg.symm
  · have hnk : n = 2 * k + 1 := by dsimp [k]; omega
    have hnr : (n : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hnk
    rw [hnr] at hb
    let z : ℤ := (k : ℤ)^2
    have hz : (z : ℝ) = (k : ℝ)^2 := by simp [z]
    have hf : (⌊(n : ℝ) / (Real.exp (4 / (n : ℝ)) - 1)⌋ : ℤ) = z := by
      rw [hnr]
      apply Int.floor_eq_iff.mpr
      constructor <;> rw [hz] <;> nlinarith only [hb.1, hb.2]
    have hg : (⌊(((n : ℝ) - 1)^2 / 4)⌋ : ℤ) = z := by
      rw [hnr]
      apply Int.floor_eq_iff.mpr
      constructor <;> rw [hz] <;> nlinarith
    exact hf.trans hg.symm

set_option pp.proofs false in
#print result
#print axioms bounds
#print axioms result

end D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor
