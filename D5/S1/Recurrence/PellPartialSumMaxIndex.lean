/- GID: D5/S1/Recurrence/PellPartialSumMaxIndex
   generality: I
   mirror-B: D5/B/S1/Recurrence/PellPartialSumMaxIndex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The greatest positive Pell index dividing an initial partial sum follows four residue classes. -/

import D5.S1.Recurrence.PellCompanionGcd
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S1.Recurrence.PellPartialSumMaxIndex

open PellCompanionGcd

/-- The initial Pell sum `P₁ + ... + Pₙ`; the included zero term is `P₀=0`. -/
def partialSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), P i

/-- Byrapuram et al., Conjecture 18: greatest positive dividing indices in all four classes. -/
theorem result :
    (∀ k : ℕ, IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k + 1)} 1) ∧
    (∀ k : ℕ, IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k + 2)} 1) ∧
    (∀ k : ℕ, 1 ≤ k →
      IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k - 1)} (2 * k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k)} (2 * k + 1)) := by
  have add (a b : ℕ) :
      P (a + b) = P a * Q b + Q a * P b ∧
      Q (a + b) = Q a * Q b + 2 * P a * P b := by
    induction b with
    | zero => simp [P, Q]
    | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        (pell_companion_step (a + b)).1, (pell_companion_step (a + b)).2,
        ih.1, ih.2, (pell_companion_step b).1, (pell_companion_step b).2]
      constructor <;> ring
  have qpos (n : ℕ) : 0 < Q n := (companion_odd n).pos
  have strict : StrictMono P := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [(pell_companion_step n).1]
    exact Nat.lt_add_of_pos_right (qpos n)
  have pos (n : ℕ) (hn : 0 < n) : 0 < P n := by
    simpa [P] using strict hn
  have pleq (n : ℕ) : P n ≤ Q n := by
    cases n with
    | zero => simp [P, Q]
    | succ n =>
      rw [(pell_companion_step n).1, (pell_companion_step n).2]
      omega
  have pltq (n : ℕ) (hn : 2 ≤ n) : P n < Q n := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [(pell_companion_step t).1, (pell_companion_step t).2]
    have := pos t (by omega)
    omega
  have parity (n : ℕ) : P n % 2 = n % 2 := by
    induction n with
    | zero => simp [P]
    | succ n ih =>
      rw [(pell_companion_step n).1, Nat.add_mod, ih]
      have hq := (companion_odd n).mod_two
      omega
  have norm (n : ℕ) :
      if n % 2 = 0 then Q n ^ 2 = 2 * P n ^ 2 + 1
      else 2 * P n ^ 2 = Q n ^ 2 + 1 := by
    induction n with
    | zero => simp [P, Q]
    | succ n ih =>
      rw [(pell_companion_step n).1, (pell_companion_step n).2]
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      split_ifs at ih ⊢ <;> (try omega) <;> nlinarith
  have sum_succ (n : ℕ) : partialSum (n + 1) = partialSum n + P (n + 1) := by
    exact Finset.sum_range_succ P (n + 1)
  have sum_closed (n : ℕ) : 2 * partialSum n + 1 = P (n + 1) + P n := by
    induction n with
    | zero => simp [partialSum, P]
    | succ n ih =>
      rw [sum_succ]
      change 2 * (partialSum n + P (n + 1)) + 1 = P (n + 2) + P (n + 1)
      rw [P]
      omega
  have double (n : ℕ) : P (2 * n) = 2 * P n * Q n ∧
      Q (2 * n) = Q n ^ 2 + 2 * P n ^ 2 := by
    simpa only [two_mul, pow_two, mul_comm, mul_left_comm, mul_assoc] using add n n
  have sums_even (r : ℕ) :
      if r % 2 = 0 then partialSum (2 * r) = 2 * P r * P (r + 1)
      else partialSum (2 * r) = Q r * Q (r + 1) := by
    have h := sum_closed (2 * r)
    rw [(pell_companion_step (2 * r)).1, (double r).1, (double r).2,
      (pell_companion_step r).1, (pell_companion_step r).2]
    have hn := norm r
    split_ifs at hn ⊢ <;> nlinarith
  have sums_odd (r : ℕ) (hr : 1 ≤ r) :
      if r % 2 = 0 then partialSum (2 * r - 1) = 2 * P r ^ 2
      else partialSum (2 * r - 1) = Q r ^ 2 := by
    have h := sum_closed (2 * r - 1)
    have hs := pell_companion_step (2 * r)
    have hp : P (2 * r + 1) = 2 * P (2 * r) + P (2 * r - 1) := by
      have he : 2 * r + 1 = (2 * r - 1) + 2 := by omega
      rw [he, P]
      congr 2
      omega
    have he : 2 * r - 1 + 1 = 2 * r := by omega
    rw [he] at h
    have hn := norm r
    have hd := (double r).2
    split_ifs at hn ⊢ <;> nlinarith
  sorry

end D5.S1.Recurrence.PellPartialSumMaxIndex
