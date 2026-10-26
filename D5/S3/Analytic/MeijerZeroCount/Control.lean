/- GID: D5/S3/Analytic/MeijerZeroCount/Control
   generality: G
   mirror-B: D5/B/S3/Analytic/MeijerZeroCount/Control
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Topology.Order.IntermediateValue, mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: A geometric-sum normalization proves the single interior control zero. -/

import D5.S3.Analytic.MeijerZeroCount.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Ring.GeomSum

open Finset Set
open D5.S3.Analytic.MeijerZeroCount.Defs
namespace D5.S3.Analytic.MeijerZeroCount.Control

private noncomputable def h (n d : ℕ) (x : ℝ) : ℝ :=
  (∑ i ∈ range n, x ^ i) - x ^ n * ∑ i ∈ range (n+d), x ^ i

private noncomputable def normalized (n d : ℕ) (x : ℝ) : ℝ :=
  (∑ i ∈ range n, x ^ ((i : ℝ) - n)) - ∑ i ∈ range (n+d), x ^ i

private lemma h_factor (n d : ℕ) (x : ℝ) :
    (x-1) * h n d x = 2*x^n - 1 - x^(2*n+d) := by
  unfold h
  rw [mul_sub, mul_left_comm (x-1) (x^n), mul_geom_sum, mul_geom_sum]
  rw [show 2*n+d = n+(n+d) by omega, pow_add]
  ring

private lemma h_normalized (n d : ℕ) {x : ℝ} (hx : 0 < x) :
    h n d x = x ^ n * normalized n d x := by
  unfold h normalized
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.rpow_sub hx, Real.rpow_natCast, Real.rpow_natCast]
  field_simp [hx.ne']

private lemma normalized_strictAnti (n d : ℕ) (hn : 0 < n) :
    StrictAntiOn (normalized n d) (Ioi 0) := by
  intro x hx y hy hxy
  unfold normalized
  have hlo : (∑ i ∈ range n, y ^ ((i : ℝ)-n)) <
      ∑ i ∈ range n, x ^ ((i : ℝ)-n) := by
    apply Finset.sum_lt_sum
    · intro i hi
      apply (Real.strictAntiOn_rpow_Ioi_of_exponent_neg _ hx hy hxy).le
      have hi' : i < n := mem_range.mp hi
      exact sub_neg.mpr (by exact_mod_cast hi')
    · refine ⟨0, mem_range.mpr hn, ?_⟩
      apply Real.strictAntiOn_rpow_Ioi_of_exponent_neg _ hx hy hxy
      simpa using (neg_neg_of_pos (show (0 : ℝ) < n by exact_mod_cast hn))
  have hhi : (∑ i ∈ range (n+d), x ^ i) ≤ ∑ i ∈ range (n+d), y ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ hx.le hxy.le i
  linarith

private lemma exists_h_zero (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    ∃ x ∈ Ioo (0 : ℝ) 1, h n d x = 0 := by
  have hc : Continuous (h n d) := by
    unfold h
    fun_prop
  have hzero : h n d 0 = 1 := by
    unfold h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [Finset.sum_range_succ']
  have hone : h n d 1 = -(d : ℝ) := by
    dsimp only [h]
    simp [Nat.cast_add]
  apply intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num) hc.continuousOn
  rw [hzero, hone]
  exact ⟨neg_neg_of_pos (by exact_mod_cast hd), by norm_num⟩

private lemma control_family (n d : ℕ) (c : ℝ) {x : ℝ} (hx : 0 < x) :
    control ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x =
      x ^ c * (2*x^n - 1 - x^(2*n+d)) := by
  dsimp only [Defs.control]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Real.rpow_add hx, Real.rpow_natCast]
  ring

private lemma control_zero_iff (n d : ℕ) (c : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    control ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x = 0 ↔
      h n d x = 0 := by
  rw [control_family n d c hx.1, ← h_factor, mul_eq_zero,
    mul_eq_zero]
  simp [(Real.rpow_pos_of_pos hx.1 c).ne', sub_ne_zero.mpr (ne_of_lt hx.2)]

/-- The control function of the two-parameter family has one interior zero. -/
theorem zeros_control (n d : ℕ) (c : ℝ) (hn : 0 < n) (hd : 0 < d) :
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧
      control ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x = 0}.encard = 1 := by
  obtain ⟨r, hr, hroot⟩ := exists_h_zero n d hn hd
  apply Set.encard_eq_one.mpr
  refine ⟨r, ?_⟩
  ext x
  constructor
  · intro hx
    have hxzero := (control_zero_iff n d c hx.1).mp hx.2
    have hrzero := hroot
    rw [h_normalized n d hx.1.1, mul_eq_zero] at hxzero
    rw [h_normalized n d hr.1, mul_eq_zero] at hrzero
    have hnx := hxzero.resolve_left (pow_ne_zero n hx.1.1.ne')
    have hnr := hrzero.resolve_left (pow_ne_zero n hr.1.ne')
    exact mem_singleton_iff.mpr ((normalized_strictAnti n d hn).injOn hx.1.1 hr.1
      (hnx.trans hnr.symm))
  · intro hx
    obtain rfl := mem_singleton_iff.mp hx
    exact ⟨hr, (control_zero_iff n d c hr).mpr hroot⟩

end D5.S3.Analytic.MeijerZeroCount.Control
