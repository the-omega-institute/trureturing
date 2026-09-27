/- GID: D5/S3/Combinatorics/ZeroQuantumPairsRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ZeroQuantumPairsRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves R. J. Mathar's 2012 recurrence conjecture for OEIS A108958, the number of unordered pairs of distinct binary words of length n with the same number of 1's (zero-quantum transitions of n spins 1/2): n(n-2)a(n) + 2(-3n^2+7n-3)a(n-1) + 4(n-1)(2n-3)a(n-2) = 0 for n >= 2. -/

/-
proof_shape: result: bind-only
escape_witness: none; every atomic fact is an instance of a pinned Mathlib lemma
  (`Nat.sum_range_choose_sq`, `Nat.sum_range_choose`, `Nat.centralBinom_eq_two_mul_choose`,
  `Nat.cast_choose_two`, `Nat.succ_mul_centralBinom_succ`), combined by sum distribution,
  `ring` and `linear_combination`
admission_basis: open-problem-resolution (issue #10598), which admits a bind-only settlement
  of an external named open problem
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ZeroQuantumPairsRecurrence

open Finset

/-- A108958: unordered pairs of distinct binary words of length `n` with the same number of 1's. -/
def a (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (n.choose k).choose 2

/-- Mathar's conjecture (OEIS A108958, formula field, 2012). -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * (n - 2) * a n + 2 * (-3 * n ^ 2 + 7 * n - 3) * a (n - 1) +
      4 * (n - 1) * (2 * n - 3) * a (n - 2) = 0

/-- The conjecture holds. -/
theorem result : claim := by
  -- the closed form `2 a(n) = C(2n, n) - 2^n`
  have closed : ∀ n, (a n : ℚ) = ((n.centralBinom : ℚ) - 2 ^ n) / 2 := by
    intro n
    have h1 : (∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℚ) ^ 2) = n.centralBinom := by
      rw [Nat.centralBinom_eq_two_mul_choose, ← Nat.sum_range_choose_sq]
      push_cast
      rfl
    have h2 : (∑ k ∈ range (n + 1), ((n.choose k : ℕ) : ℚ)) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    simp only [a, Nat.cast_sum, Nat.cast_choose_two]
    rw [← h1, ← h2, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hU1 := Nat.succ_mul_centralBinom_succ m
  have hU2 := Nat.succ_mul_centralBinom_succ (m + 1)
  have q1 : ((m : ℚ) + 1) * ((m + 1).centralBinom : ℚ) =
      2 * (2 * m + 1) * (m.centralBinom : ℚ) := by
    exact_mod_cast hU1
  have hU2' : (m + 2) * (m + 2).centralBinom = 2 * (2 * m + 3) * (m + 1).centralBinom := by
    rw [show m + 2 = m + 1 + 1 from rfl, show 2 * m + 3 = 2 * (m + 1) + 1 by ring]
    exact hU2
  have q2 : ((m : ℚ) + 2) * ((m + 2).centralBinom : ℚ) =
      2 * (2 * m + 3) * ((m + 1).centralBinom : ℚ) := by
    exact_mod_cast hU2'
  have key : ((m + 2 : ℕ) : ℚ) * ((m + 2 : ℕ) - 2) * a (m + 2) +
      2 * (-3 * ((m + 2 : ℕ) : ℚ) ^ 2 + 7 * ((m + 2 : ℕ) : ℚ) - 3) * a (m + 2 - 1) +
      4 * (((m + 2 : ℕ) : ℚ) - 1) * (2 * ((m + 2 : ℕ) : ℚ) - 3) * a (m + 2 - 2) = 0 := by
    rw [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl, closed, closed, closed]
    push_cast
    linear_combination ((m : ℚ) / 2) * q2 - ((m : ℚ) + 1) * q1
  exact_mod_cast key

end D5.S3.Combinatorics.ZeroQuantumPairsRecurrence
