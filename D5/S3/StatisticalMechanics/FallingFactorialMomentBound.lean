/- GID: D5/S3/StatisticalMechanics/FallingFactorialMomentBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/FallingFactorialMomentBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: n^2/k (1/k)^n k!/(k-n)! <= 1 for all 0 <= n <= k (conjecture of arXiv:2004.07168). -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  polynomial inequalities for n ≤ 3 and, for n ≥ 4, the product bound
  ∏ (1 - i/k) ≤ exp(-n(n-1)/(2k)) with u e^(-u) ≤ e^(-1) < 3/8
admission_basis: open-problem-resolution (issue #11361)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.FallingFactorialMomentBound

open Finset Real Nat

/-- The conjecture after eq. (003.21) of arXiv:2004.07168: for every integer `k ≥ 1` and every
integer `0 ≤ n ≤ k`, `n² / k · (1 / k)^n · k! / (k - n)! ≤ 1`. -/
def claim : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, n ≤ k →
    (n : ℝ) ^ 2 / k * (1 / k) ^ n * ((k ! : ℝ) / ((k - n) ! : ℝ)) ≤ 1

/-- The conjecture holds. -/
theorem result : claim := by
  intro k hk n hn
  -- the integer form `n² · k(k-1)⋯(k-n+1) ≤ k^(n+1)`
  have nat_bound : n ^ 2 * k.descFactorial n ≤ k ^ (n + 1) := by
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · simp
      · simp only [Nat.descFactorial_one, one_pow, one_mul]
        exact Nat.le_self_pow (by norm_num) k
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
        rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 0 = m + 2 by omega]
        have h : (m + 2) ^ (2 + 1) = 2 ^ 2 * ((m + 1) * ((m + 2) * 1)) + (m + 2) * m ^ 2 := by ring
        rw [h]; exact Nat.le_add_right _ _
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
        rw [show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega,
          show m + 3 - 0 = m + 3 by omega]
        have h : (m + 3) ^ (3 + 1) =
            3 ^ 2 * ((m + 1) * ((m + 2) * ((m + 3) * 1))) + (m + 3) * (m ^ 3 + 9) := by ring
        rw [h]; exact Nat.le_add_right _ _
    · have hk : 0 < k := by omega
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast h4
      have hnk : (n : ℝ) ≤ k := by exact_mod_cast hn
      -- the falling factorial as `k^n ∏ (1 - i/k)`
      have hprod : (k.descFactorial n : ℝ) = (k : ℝ) ^ n * ∏ i ∈ range n, (1 - (i : ℝ) / k) := by
        rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
          show (k : ℝ) ^ n = ∏ _i ∈ range n, (k : ℝ) by rw [prod_const, card_range],
          ← prod_mul_distrib]
        refine prod_congr rfl fun i hi => ?_
        have hi' : i < n := mem_range.mp hi
        rw [Nat.cast_sub (by omega)]
        field_simp
      -- `1 - x ≤ e^{-x}` termwise
      have hbound : ∏ i ∈ range n, (1 - (i : ℝ) / k) ≤ exp (-(∑ i ∈ range n, (i : ℝ) / k)) := by
        rw [← sum_neg_distrib, Real.exp_sum]
        refine prod_le_prod (fun i hi => ?_)
          (fun i _ => by linarith [Real.add_one_le_exp (-((i : ℝ) / k))])
        have hi' : (i : ℝ) < n := by exact_mod_cast mem_range.mp hi
        rw [sub_nonneg, div_le_one hkR]
        linarith
      -- `∑_{i<n} i / k = n (n-1) / (2k)`
      have hsum : ∑ i ∈ range n, (i : ℝ) / k = (n : ℝ) * (n - 1) / (2 * k) := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        have h := Finset.sum_range_id_mul_two n
        have h' : (∑ i ∈ range n, (i : ℝ)) * 2 = (n : ℝ) * (n - 1) := by
          have := congrArg (fun m : ℕ => (m : ℝ)) h
          push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at this
          exact this
        field_simp
        linarith
      set u : ℝ := (n : ℝ) * (n - 1) / (2 * k) with hu
      clear_value u
      have hu0 : 0 ≤ u := by
        rw [hu]; exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      -- `u e^{-u} ≤ e^{-1} < 3/8`
      have hue : u * exp (-u) ≤ exp (-1) := by
        have h := Real.add_one_le_exp (u - 1)
        have : exp (u - 1) = exp u * exp (-1) := by rw [sub_eq_add_neg, Real.exp_add]
        rw [this] at h
        have hpos : 0 < exp u := Real.exp_pos u
        have hneg : exp (-u) * exp u = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-u), Real.exp_pos (-1)]
      have he : exp (-1) < 3 / 8 := by
        have h := Real.exp_one_gt_d9
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      -- `n² e^{-u} ≤ k`
      have hmain : (n : ℝ) ^ 2 * exp (-u) ≤ k := by
        have hku : (k : ℝ) * u * 2 = (n : ℝ) * (n - 1) := by rw [hu]; field_simp
        have h1 : ((n : ℝ) - 1) * ((n : ℝ) ^ 2 * exp (-u)) = 2 * n * k * (u * exp (-u)) := by
          linear_combination (-(n * exp (-u))) * hku
        have h2 : 2 * (n : ℝ) * k * (u * exp (-u)) ≤ 2 * n * k * (3 / 8) := by
          have := lt_of_le_of_lt hue he
          have hnk0 : 0 ≤ 2 * (n : ℝ) * k := by positivity
          nlinarith
        have h3 : 2 * (n : ℝ) * k * (3 / 8) ≤ ((n : ℝ) - 1) * k := by nlinarith
        have hn1 : 0 < (n : ℝ) - 1 := by linarith
        nlinarith
      have hbound' : ∏ i ∈ range n, (1 - (i : ℝ) / k) ≤ exp (-u) := by rw [← hsum]; exact hbound
      have hreal : ((n ^ 2 * k.descFactorial n : ℕ) : ℝ) ≤ ((k ^ (n + 1) : ℕ) : ℝ) := by
        push_cast
        rw [hprod]
        have hkn : (0 : ℝ) ≤ (k : ℝ) ^ n := by positivity
        calc (n : ℝ) ^ 2 * ((k : ℝ) ^ n * ∏ i ∈ range n, (1 - (i : ℝ) / k))
            ≤ (n : ℝ) ^ 2 * ((k : ℝ) ^ n * exp (-u)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound' hkn) (by positivity)
        _ = (k : ℝ) ^ n * ((n : ℝ) ^ 2 * exp (-u)) := by ring
        _ ≤ (k : ℝ) ^ n * k := mul_le_mul_of_nonneg_left hmain hkn
        _ = (k : ℝ) ^ (n + 1) := by ring
      exact_mod_cast hreal
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfact : (k ! : ℝ) / ((k - n) ! : ℝ) = (k.descFactorial n : ℝ) := by
    rw [← Nat.factorial_mul_descFactorial hn]
    push_cast
    field_simp
  rw [hfact]
  have hb : ((n ^ 2 * k.descFactorial n : ℕ) : ℝ) ≤ ((k ^ (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast nat_bound
  push_cast at hb
  have hpow : (0 : ℝ) < (k : ℝ) ^ (n + 1) := by positivity
  calc (n : ℝ) ^ 2 / k * (1 / k) ^ n * (k.descFactorial n : ℝ)
      = (n : ℝ) ^ 2 * (k.descFactorial n : ℝ) / (k : ℝ) ^ (n + 1) := by
        rw [one_div_pow, pow_succ]
        field_simp
        ring
    _ ≤ 1 := by rw [div_le_one hpow]; exact hb

end D5.S3.StatisticalMechanics.FallingFactorialMomentBound
