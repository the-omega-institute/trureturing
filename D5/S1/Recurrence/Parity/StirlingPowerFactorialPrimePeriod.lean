/- GID: D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Inclusion-exclusion and a prime window prove Bala's A122399 periodicity conjecture. -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime periods of the Stirling power-factorial sum

The definition of `a` is the finite sum in OEIS A122399. Inclusion-exclusion
turns its reduction modulo a prime into a fixed finite sum of powers. Fermat's
little theorem then proves Peter Bala's May 31, 2022 conjecture for all positive
indices. The asserted period is `p - 1`; minimality is not asserted.
-/

open Finset

namespace D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod

private def expansion (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1) ^ (k - j) * (Nat.choose k j : ℤ) * (j : ℤ) ^ n

private theorem expansion_zero (k : ℕ) : expansion 0 k = if k = 0 then 1 else 0 := by
  have h := add_pow (1 : ℤ) (-1) k
  have he : expansion 0 k = (1 + (-1) : ℤ) ^ k := by
    rw [h]
    apply sum_congr rfl
    intro j hj
    simp [mul_comm]
  rw [he]
  split_ifs with hk
  · simp [hk]
  · simp [hk]

-- The binomial identity makes the alternating sum obey the weighted Stirling recurrence.
private theorem expansion_succ (n k : ℕ) :
    expansion (n + 1) (k + 1) = (k + 1 : ℤ) *
      (expansion n (k + 1) + expansion n k) := by
  have term (j : ℕ) (hj : j ≤ k) :
      (-1 : ℤ) ^ (k + 1 - j) * (Nat.choose (k + 1) j : ℤ) * (j : ℤ) ^ (n + 1) =
      (k + 1 : ℤ) * ((-1 : ℤ) ^ (k + 1 - j) * (Nat.choose (k + 1) j : ℤ) *
        (j : ℤ) ^ n + (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) * (j : ℤ) ^ n) := by
    have hc := congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_mul_succ_eq k j)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (by omega : j ≤ k + 1)] at hc
    rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ (-1 : ℤ), pow_succ]
    linear_combination -((-1 : ℤ) ^ (k - j) * (j : ℤ) ^ n) * hc
  unfold expansion
  rw [sum_range_succ _ (k + 1), sum_range_succ _ (k + 1)]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, mul_one,
    Nat.cast_add]
  have hs := sum_congr (s₁ := range (k + 1)) rfl
    (fun j hj => term j (by simpa using mem_range.mp hj))
  rw [hs, ← mul_sum, sum_add_distrib, pow_succ]
  ring

/-- Inclusion-exclusion for the factorial-weighted Mathlib Stirling numbers. -/
theorem stirling2_inclusion_exclusion (n k : ℕ) :
    (k.factorial * Nat.stirlingSecond n k : ℤ) =
      ∑ j ∈ range (k + 1), (-1) ^ (k - j) * (Nat.choose k j : ℤ) * (j : ℤ) ^ n := by
  change _ = expansion n k
  induction n generalizing k with
  | zero =>
    rw [expansion_zero]
    cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp [expansion]
    | succ k =>
      rw [expansion_succ, ← ih, ← ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

/-- OEIS A122399, with the entry's offset-zero finite-sum definition. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), k ^ n * k.factorial * Nat.stirlingSecond n k

/-- The reduction has a fixed prime-sized window, including at index zero. -/
theorem a_eq_window (p n : ℕ) (hp : p.Prime) :
    (a n : ZMod p) =
      ∑ k ∈ range p, ((k ^ n * k.factorial * Nat.stirlingSecond n k : ℕ) : ZMod p) := by
  simp only [a, Nat.cast_sum]
  rcases le_total (n + 1) p with h | h
  · apply sum_subset (range_mono h)
    intro k _ hk
    have hnk : n < k := by simp only [mem_range] at hk; omega
    simp [Nat.stirlingSecond_eq_zero_of_lt hnk]
  · symm
    apply sum_subset (range_mono h)
    intro k _ hk
    have hpk : p ≤ k := by simpa only [mem_range, not_lt] using hk
    have hf : (k.factorial : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hp.pos hpk)
    simp only [Nat.cast_mul, hf, mul_zero, zero_mul]

private theorem a_eq_double_sum (p n : ℕ) (hp : p.Prime) :
    (a n : ZMod p) = ∑ k ∈ range p, ∑ j ∈ range (k + 1),
      (-1 : ZMod p) ^ (k - j) * (Nat.choose k j : ZMod p) *
        ((k : ZMod p) * (j : ZMod p)) ^ n := by
  rw [a_eq_window p n hp]
  apply sum_congr rfl
  intro k hk
  have hi := congrArg (Int.castRingHom (ZMod p)) (stirling2_inclusion_exclusion n k)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  push_cast
  rw [mul_assoc, hi, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring

private theorem power_period (p : ℕ) (hp : p.Prime) (x : ZMod p)
    (n : ℕ) (hn : 1 ≤ n) : x ^ (n + (p - 1)) = x ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · simp [hx, show n ≠ 0 by omega]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]

/-- Bala's conjecture for OEIS A122399. The period need not be minimal. -/
theorem bala_conjecture (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    (a (n + (p - 1)) : ZMod p) = a n := by
  rw [a_eq_double_sum p _ hp, a_eq_double_sum p _ hp]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [power_period p hp _ n hn]

/-- Every nonnegative multiple of the period preserves each positive-index term. -/
theorem bala_conjecture_periodic (p : ℕ) (hp : p.Prime) (n m : ℕ) (hn : 1 ≤ n) :
    (a (n + m * (p - 1)) : ZMod p) = a n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, bala_conjecture p hp _ (by omega), ih]

#print axioms stirling2_inclusion_exclusion
#print axioms a_eq_window
#print axioms bala_conjecture
#print axioms bala_conjecture_periodic

end D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod
