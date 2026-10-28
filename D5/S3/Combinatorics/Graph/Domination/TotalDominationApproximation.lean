/- GID: D5/S3/Combinatorics/Graph/Domination/TotalDominationApproximation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TotalDominationApproximation
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Joint logarithmic radius and angle approximation for actual total roots. -/

import D5.S3.Combinatorics.Graph.Domination.TotalDominationBlowup
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Round

/-!
The logarithmic power-root approximation is an elementary ingredient on the
original whole-plane total-domination route, not a density assumption.
The graph consumer retains actual subset counts and every selected-vertex condition.
-/
set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TotalDominationApproximation

open Complex
open scoped Real

/-- A single integer branch controls the angle while preserving the exact power. -/
private theorem logarithmic_grid (t α θ : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ v : ℂ, (Complex.exp v) ^ k = Complex.exp ((t : ℂ) + (α : ℂ) * I) ∧
      v.re = t / k ∧ |v.im - θ| ≤ Real.pi / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  let j : ℤ := round (((k : ℝ) * θ - α) / (2 * Real.pi))
  let β : ℝ := (α + 2 * Real.pi * j) / k
  let v : ℂ := (t / k : ℝ) + (β : ℂ) * I
  have hv : (k : ℂ) * v = (t : ℂ) + (α : ℂ) * I +
      (j : ℂ) * (2 * Real.pi * I) := by
    dsimp [v, β]
    push_cast
    field_simp
    <;> ring
  refine ⟨v, ?_, by simp [v], ?_⟩
  · rw [← Complex.exp_nat_mul, hv, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]
  · have hj := abs_sub_round (((k : ℝ) * θ - α) / (2 * Real.pi))
    have hβ : β - θ = -(2 * Real.pi / k) *
        (((k : ℝ) * θ - α) / (2 * Real.pi) - j) := by
      dsimp [β]
      field_simp
      <;> ring
    change |β - θ| ≤ Real.pi / k
    rw [hβ, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi / k)]
    have hmul := mul_le_mul_of_nonneg_left hj
      (by positivity : 0 ≤ 2 * Real.pi / k)
    nlinarith

/-- Both logarithmic coordinates are approximated with the same integer exponent. -/
theorem joint_power_root_approximation (ξ : ℂ) (hξ : ξ.re ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ t α : ℝ, (N : ℝ) + 2 < t / ξ.re →
      ∃ (k : ℕ) (w : ℂ), 0 < k ∧
        w ^ k = Complex.exp ((t : ℂ) + (α : ℂ) * I) ∧
        ‖w - Complex.exp ξ‖ < ε := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    Complex.continuous_exp.continuousAt ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((|ξ.re| + Real.pi) / δ)
  refine ⟨N, ?_⟩
  intro t α hp
  let p : ℝ := t / ξ.re
  let k : ℕ := ⌊p⌋₊
  have hp0 : 0 ≤ p := by dsimp [p]; nlinarith [Nat.cast_nonneg N]
  have hkN : (N : ℝ) < k := by
    have hf := Nat.sub_one_lt_floor p
    change (N : ℝ) < (⌊p⌋₊ : ℝ)
    dsimp [p] at hf
    linarith
  have hkR : (0 : ℝ) < k := lt_of_le_of_lt (Nat.cast_nonneg N) hkN
  have hk : 0 < k := by exact_mod_cast hkR
  have hf0 : 0 ≤ p - k := Nat.zero_le_self_sub_floor hp0
  have hf1 : p - k < 1 := Nat.self_sub_floor_lt_one p
  have hr : |t / k - ξ.re| ≤ |ξ.re| / k := by
    have hid : t / k - ξ.re = ξ.re * (p - k) / k := by
      dsimp [p]
      field_simp
      <;> ring
    rw [hid, abs_div, abs_mul, abs_of_pos hkR, abs_of_nonneg hf0]
    apply div_le_div_of_nonneg_right _ hkR.le
    exact mul_le_of_le_one_right (abs_nonneg _) hf1.le
  obtain ⟨v, hv, hre, him⟩ := logarithmic_grid t α ξ.im k hk
  have hvδ : ‖v - ξ‖ < δ := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im (v - ξ)
    have hlt : (|ξ.re| + Real.pi) / k < δ := by
      apply (div_lt_iff₀ hkR).mpr
      have hN' : |ξ.re| + Real.pi < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
      nlinarith
    have hs : |(v - ξ).re| + |(v - ξ).im| ≤ (|ξ.re| + Real.pi) / k := by
      simp only [sub_re, sub_im, hre]
      calc
        |t / k - ξ.re| + |v.im - ξ.im| ≤ |ξ.re| / k + Real.pi / k := add_le_add hr him
        _ = _ := by ring
    exact lt_of_le_of_lt (hnorm.trans hs) hlt
  refine ⟨k, Complex.exp v, hk, hv, ?_⟩
  exact hcont (by simpa [dist_eq_norm] using hvδ)

#print axioms joint_power_root_approximation

end D5.S3.Combinatorics.Graph.Domination.TotalDominationApproximation
