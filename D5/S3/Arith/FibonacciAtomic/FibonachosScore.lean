/- GID: D5/S3/Arith/FibonacciAtomic/FibonachosScore
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FibonachosScore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Fibonachos ties and large-heap majority follow Fibonacci blocks. -/

import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Arith.FibonacciAtomic.FibonachosScore

open scoped BigOperators

/-- Scores of the player to move and the other player. Each positive heap
uses the next Fibonacci number, resetting its index to one when it exceeds
the heap. The scores swap at every move, exactly as in OEIS A382814's
program. Index zero is treated as a reset; reachable indices are positive.
The remaining heap decreases by at least one at each move. -/
def play (n i : ℕ) : ℕ × ℕ :=
  if _hn : n = 0 then (0, 0) else
    let j := if 0 < Nat.fib i ∧ Nat.fib i ≤ n then i else 1
    let q := play (n - Nat.fib j) (j + 1)
    (Nat.fib j + q.2, q.1)
termination_by n
 decreasing_by
  have hp : 0 < Nat.fib (if 0 < Nat.fib i ∧ Nat.fib i ≤ n then i else 1) := by
    split
    · exact (by assumption : 0 < Nat.fib i ∧ Nat.fib i ≤ n).1
    · simp
  exact Nat.sub_lt (Nat.pos_of_ne_zero _hn) hp

/-- Number collected by the first player, with the initial index one. -/
def a (n : ℕ) : ℕ := (play n 1).1

/-- Signed advantage of the player to move. -/
def advantage (n i : ℕ) : ℤ := (play n i).1 - (play n i).2

set_option maxHeartbeats 2000000 in
-- The proof includes kernel-checked finite heap computations and a uniform bound.
/-- Kagey's tie and large-heap majority conjectures. The interval endpoints
use additive inequalities to express the original natural-number endpoints
without truncated subtraction. -/
theorem result :
    (∀ n : ℕ, 1 ≤ n → (2 * a n = n ↔ n ∈ ({2, 8, 10, 32} : Finset ℕ))) ∧
    (∀ n : ℕ, 32 < n → (n < 2 * a n ↔
      ∃ m : ℕ, Odd m ∧ Nat.fib m ≤ n + 1 ∧ n + 2 ≤ Nat.fib (m + 1))) := by
  have zero (i : ℕ) : play 0 i = (0, 0) := by rw [play]; simp
  have conserve (n i : ℕ) : (play n i).1 + (play n i).2 = n := by
    induction n using Nat.strong_induction_on generalizing i with
    | h n ih =>
      by_cases hn : n = 0
      · subst n; simp [zero]
      · let j := if 0 < Nat.fib i ∧ Nat.fib i ≤ n then i else 1
        have hj : 0 < Nat.fib j ∧ Nat.fib j ≤ n := by
          dsimp [j]; split
          · assumption
          · simp; omega
        have hh := ih (n - Nat.fib j) (Nat.sub_lt (by omega) hj.1) (j + 1)
        rw [play, dif_neg hn]
        change Nat.fib j + (play (n - Nat.fib j) (j + 1)).2 +
          (play (n - Nat.fib j) (j + 1)).1 = n
        omega
  have step (n i : ℕ) (hi : 0 < i) (hfit : Nat.fib i ≤ n) (hn : 0 < n) :
      advantage n i = (Nat.fib i : ℤ) - advantage (n - Nat.fib i) (i + 1) := by
    unfold advantage
    rw [play, dif_neg (by omega : n ≠ 0), if_pos ⟨Nat.fib_pos.mpr hi, hfit⟩]
    simp only [Nat.cast_add]
    ring
  have reset (n i : ℕ) (hn : n < Nat.fib i) : advantage n i = advantage n 1 := by
    by_cases hzero : n = 0
    · subst n; simp [advantage, zero]
    · unfold advantage
      have hnpos : 0 < n := by omega
      rw [play, dif_neg hzero, if_neg (by omega : ¬ (0 < Nat.fib i ∧ Nat.fib i ≤ n))]
      rw [play.eq_def n 1, dif_neg hzero, if_pos (by simp; omega)]
  have score (n : ℕ) : advantage n 1 = 2 * (a n : ℤ) - n := by
    have hh := conserve n 1
    unfold advantage a
    omega
  have azero : advantage 0 1 = 0 := by simp [advantage, zero]
  have initial : (List.range' 1 10).map a = [1, 1, 2, 3, 3, 4, 3, 4, 4, 5] := by
    cbv
  have prefix_run (k n : ℕ) (hfit : Nat.fib (k + 2) ≤ n + 1) :
      advantage n 1 = (∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * Nat.fib (j + 1)) +
        (-1 : ℤ) ^ k * advantage (n - (Nat.fib (k + 2) - 1)) (k + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hf : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
        Nat.fib_add_two
      have hp := Nat.fib_pos.mpr (by omega : 0 < k + 2)
      have hk : Nat.fib (k + 2) ≤ n + 1 :=
        (Nat.fib_mono (by omega)).trans hfit
      have htake : Nat.fib (k + 1) ≤ n - (Nat.fib (k + 2) - 1) := by omega
      have hpos : 0 < n - (Nat.fib (k + 2) - 1) :=
        (Nat.fib_pos.mpr (by omega : 0 < k + 1)).trans_le htake
      have hsub : n - (Nat.fib (k + 2) - 1) - Nat.fib (k + 1) =
          n - (Nat.fib (k + 1 + 2) - 1) := by omega
      rw [ih hk, step _ _ (by omega) htake hpos, hsub,
        Finset.sum_range_succ, pow_succ]
      ring
  have alternating (k : ℕ) :
      (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * Nat.fib (j + 1)) =
        1 + (-1 : ℤ) ^ k * Nat.fib k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.fib_add_two, pow_succ]
      push_cast
      ring
  have block (k n : ℕ) (hlo : Nat.fib (k + 3) ≤ n + 1)
      (hhi : n + 2 ≤ Nat.fib (k + 4)) :
      let r := n - (Nat.fib (k + 3) - 1)
      r < Nat.fib (k + 2) ∧
      advantage n 1 = 1 + (-1 : ℤ) ^ (k + 3) * (advantage r 1 - Nat.fib k) := by
    dsimp only
    have hf : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
      Nat.fib_add_two
    have hp := Nat.fib_pos.mpr (by omega : 0 < k + 3)
    have hr : n - (Nat.fib (k + 3) - 1) < Nat.fib (k + 2) := by omega
    refine ⟨hr, ?_⟩
    have hrun := prefix_run (k + 1) n hlo
    rw [alternating k, reset _ _ hr] at hrun
    rw [hrun]
    simp only [pow_succ]
    ring
  have uniform (k u : ℕ) (hu : u < Nat.fib (k + 4)) :
      1 - (Nat.fib (k + 1) : ℤ) ≤ advantage u 1 ∧
      advantage u 1 ≤ 1 + (Nat.fib (k + 1) : ℤ) := by
    induction k using Nat.strong_induction_on generalizing u with
    | h k ih =>
      by_cases hk : k < 2
      · interval_cases k <;> norm_num [Nat.fib] at hu
        · interval_cases u <;> cbv <;> exact ⟨.mk _, .mk _⟩
        · interval_cases u <;> cbv <;> exact ⟨.mk _, .mk _⟩
      · have htwo : 2 ≤ k := by omega
        by_cases hsmall : u < Nat.fib (k + 3)
        · have hh := ih (k - 1) (by omega) u
            (by simpa only [show k - 1 + 4 = k + 3 by omega] using hsmall)
          have hm := Nat.fib_mono (show k ≤ k + 1 by omega)
          have he : k - 1 + 1 = k := by omega
          rw [he] at hh
          constructor <;> omega
        · by_cases hlast : u + 1 = Nat.fib (k + 4)
          · have hh := (block (k + 1) u (by change Nat.fib (k + 4) ≤ u + 1; omega) (by
                change u + 2 ≤ Nat.fib (k + 5)
                have hp : Nat.fib (k + 4) < Nat.fib (k + 5) :=
                  Nat.fib_lt_fib_succ (by omega)
                omega)).2
            have hz : u - (Nat.fib (k + 1 + 3) - 1) = 0 := by
              change u - (Nat.fib (k + 4) - 1) = 0
              omega
            rw [hz, azero] at hh
            rcases Nat.even_or_odd (k + 1 + 3) with he | ho
            · rw [he.neg_one_pow] at hh; constructor <;> omega
            · rw [ho.neg_one_pow] at hh; constructor <;> omega
          · have hh := block k u (by omega) (by omega)
            have hr := ih (k - 2) (by omega) (u - (Nat.fib (k + 3) - 1))
              (by simpa [show k - 2 + 4 = k + 2 by omega] using hh.1)
            have he : k - 2 + 1 = k - 1 := by omega
            rw [he] at hr
            have hf : Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k := by
              have h := Nat.fib_add_two (n := k - 1)
              simpa only [show k - 1 + 2 = k + 1 by omega,
                show k - 1 + 1 = k by omega] using h
            have hm := Nat.fib_mono (show k - 1 ≤ k by omega)
            have hp := Nat.fib_pos.mpr (show 0 < k + 1 by omega)
            rcases Nat.even_or_odd (k + 3) with he | ho
            · have hd := hh.2; rw [he.neg_one_pow] at hd; constructor <;> omega
            · have hd := hh.2; rw [ho.neg_one_pow] at hd; constructor <;> omega
  have locate (n : ℕ) (hn : 1 ≤ n) :
      ∃ k : ℕ, Nat.fib (k + 3) ≤ n + 1 ∧ n + 2 ≤ Nat.fib (k + 4) := by
    let m := Nat.greatestFib (n + 1)
    have hm : 3 ≤ m := by
      apply Nat.le_greatestFib.mpr
      norm_num [Nat.fib]
      omega
    have hlo := Nat.fib_greatestFib_le (n + 1)
    have hhi := Nat.lt_fib_greatestFib_add_one (n + 1)
    refine ⟨m - 3, ?_, ?_⟩
    · simpa only [show m - 3 + 3 = m by omega] using hlo
    · rw [show m - 3 + 4 = m + 1 by omega]
      exact hhi
  have unique (n m : ℕ) (hlo : Nat.fib m ≤ n + 1)
      (hhi : n + 2 ≤ Nat.fib (m + 1)) : m = Nat.greatestFib (n + 1) := by
    have h₁ : m ≤ Nat.greatestFib (n + 1) := Nat.le_greatestFib.mpr hlo
    have h₂ : Nat.greatestFib (n + 1) < m + 1 := Nat.greatestFib_lt.mpr (by omega)
    omega
  have signs (k n : ℕ) (hk : 6 ≤ k) (hlo : Nat.fib (k + 3) ≤ n + 1)
      (hhi : n + 2 ≤ Nat.fib (k + 4)) :
      (Odd (k + 3) → 0 < advantage n 1) ∧
      (Even (k + 3) → advantage n 1 < 0) := by
    have hb := block k n hlo hhi
    have hr := uniform (k - 2) (n - (Nat.fib (k + 3) - 1))
      (by simpa only [show k - 2 + 4 = k + 2 by omega] using hb.1)
    rw [show k - 2 + 1 = k - 1 by omega] at hr
    have hf : Nat.fib k = Nat.fib (k - 2) + Nat.fib (k - 1) := by
      have h := Nat.fib_add_two (n := k - 2)
      simpa only [show k - 2 + 2 = k by omega,
        show k - 2 + 1 = k - 1 by omega] using h
    have hthree : 3 ≤ Nat.fib (k - 2) := by
      have hh := Nat.fib_mono (show 4 ≤ k - 2 by omega)
      norm_num [Nat.fib] at hh
      exact hh
    constructor
    · intro ho; have hd := hb.2; rw [ho.neg_one_pow] at hd; omega
    · intro he; have hd := hb.2; rw [he.neg_one_pow] at hd; omega
  have large (n : ℕ) (hn : 32 < n) :
      ∃ m : ℕ, 9 ≤ m ∧ Nat.fib m ≤ n + 1 ∧ n + 2 ≤ Nat.fib (m + 1) ∧
        (0 < advantage n 1 ↔ Odd m) ∧ advantage n 1 ≠ 0 := by
    obtain ⟨k, hlo, hhi⟩ := locate n (by omega)
    have hk : 6 ≤ k := by
      by_contra h
      have hh := Nat.fib_mono (show k + 4 ≤ 9 by omega)
      have h9 : Nat.fib 9 = 34 := by decide
      omega
    have hs := signs k n hk hlo hhi
    refine ⟨k + 3, by omega, hlo, hhi, ?_, ?_⟩
    · constructor
      · intro hpos
        rcases Nat.even_or_odd (k + 3) with he | ho
        · have hh := hs.2 he; omega
        · exact ho
      · exact hs.1
    · rcases Nat.even_or_odd (k + 3) with he | ho
      · have hh := hs.2 he; omega
      · have hh := hs.1 ho; omega
  have small (n : ℕ) (hn : 1 ≤ n) (h32 : n ≤ 32) :
      2 * a n = n ↔ n ∈ ({2, 8, 10, 32} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases n <;> cbv <;> simp
  constructor
  · intro n hn
    by_cases h32 : n ≤ 32
    · exact small n hn h32
    · obtain ⟨m, hm, hlo, hhi, hs, hne⟩ := large n (by omega)
      have hscore := score n
      have htie : ¬ 2 * a n = n := by intro h; apply hne; omega
      have hmem : n ∉ ({2, 8, 10, 32} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact iff_of_false htie hmem
  · intro n hn
    obtain ⟨m, hm, hlo, hhi, hs, hne⟩ := large n hn
    have hscore := score n
    have hcompare : n < 2 * a n ↔ 0 < advantage n 1 := by omega
    rw [hcompare, hs]
    constructor
    · intro ho; exact ⟨m, ho, hlo, hhi⟩
    · rintro ⟨j, hj, hjlo, hjhi⟩
      have he : j = m := (unique n j hjlo hjhi).trans (unique n m hlo hhi).symm
      simpa only [he] using hj

end D5.S3.Arith.FibonacciAtomic.FibonachosScore
