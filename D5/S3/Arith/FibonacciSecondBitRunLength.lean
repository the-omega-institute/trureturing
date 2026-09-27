/- GID: D5/S3/Arith/FibonacciSecondBitRunLength
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciSecondBitRunLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No three consecutive Fibonacci numbers carry the same second most significant binary digit. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciSecondBitRunLength

/-
proof_shape: result: content
escape_witness: the active path carries three intermediate facts, none of them an
  instantiation, projection or normalisation of a pinned upstream statement:
  (i) the window `2 * 2 ^ (size m - 2) ≤ m < 4 * 2 ^ (size m - 2)` for `m ≥ 2`, which names the
      pair of consecutive powers of two that brackets `m`;
  (ii) `bitOf`, which reads the second digit off any such bracketing: inside a window the
      digit is one exactly when `3 * 2 ^ L ≤ m`, obtained by pinning `size m = L + 2` and
      evaluating the quotient, which lies in `{2, 3}`;
  (iii) the two-sided bound `8 * fib n ≤ 5 * fib (n+1)` and `8 * fib (n+1) ≤ 13 * fib n` for
      `n ≥ 5`, whose content is that the interval `[8/5, 13/8]` is carried into itself by
      `x ↦ 1 + 1/x`, so each half of the bound feeds the other across the induction step.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- The second most significant binary digit of `m`. -/
def secondBit (m : ℕ) : ℕ := m / 2 ^ (Nat.size m - 2) % 2

/-- The conjecture recorded on the sequence of second most significant binary digits of the
Fibonacci numbers exceeding one: no three consecutive entries agree. The sequence starts at
`fib 3 = 2`, the first Fibonacci number with a second binary digit. -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ¬ (secondBit (Nat.fib n) = secondBit (Nat.fib (n + 1)) ∧
       secondBit (Nat.fib (n + 1)) = secondBit (Nat.fib (n + 2)))

/-- The conjecture holds. -/
theorem result : claim := by
  have sizeWindow : ∀ m : ℕ, 2 ≤ m →
      2 * 2 ^ (Nat.size m - 2) ≤ m ∧ m < 4 * 2 ^ (Nat.size m - 2) := by
    intro m hm
    have hs2 : 2 ≤ Nat.size m := Nat.lt_size.mpr (by simpa using hm)
    constructor
    · have h : (2 : ℕ) ^ (Nat.size m - 1) ≤ m := Nat.lt_size.mp (by omega)
      have e : 2 * 2 ^ (Nat.size m - 2) = 2 ^ (Nat.size m - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    · have h : m < 2 ^ Nat.size m := Nat.lt_size_self m
      have e : (4 : ℕ) * 2 ^ (Nat.size m - 2) = 2 ^ (Nat.size m) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]; congr 1; omega
      omega
  have bitOf : ∀ m L : ℕ, 2 * 2 ^ L ≤ m → m < 4 * 2 ^ L →
      (secondBit m = 1 ↔ 3 * 2 ^ L ≤ m) := by
    intro m L h1 h2
    have hp : 0 < (2 : ℕ) ^ L := by positivity
    have hsize : Nat.size m = L + 2 := by
      have hlt : m < 2 ^ (L + 2) := by
        have e : (4 : ℕ) * 2 ^ L = 2 ^ (L + 2) := by ring
        omega
      have hge : (2 : ℕ) ^ (L + 1) ≤ m := by
        have e : (2 : ℕ) * 2 ^ L = 2 ^ (L + 1) := by ring
        omega
      have h3 : Nat.size m ≤ L + 2 := Nat.size_le.mpr hlt
      have h4 : L + 1 < Nat.size m := Nat.lt_size.mpr hge
      omega
    rw [secondBit, hsize]
    simp only [Nat.add_sub_cancel]
    have hd2 : 2 ≤ m / 2 ^ L := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    have hd4 : m / 2 ^ L < 4 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have hd3 : 3 ≤ m / 2 ^ L ↔ 3 * 2 ^ L ≤ m := Nat.le_div_iff_mul_le hp
    interval_cases h : (m / 2 ^ L) <;> omega
  have bounds : ∀ n : ℕ, 5 ≤ n →
      8 * Nat.fib n ≤ 5 * Nat.fib (n + 1) ∧ 8 * Nat.fib (n + 1) ≤ 13 * Nat.fib n := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro hk1
      rcases Nat.lt_or_ge k 5 with hk | hk
      · have : k = 4 := by omega
        subst this; decide
      · obtain ⟨h1, h2⟩ := ih (by omega)
        have hfk : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
        omega
  intro n hn h
  obtain ⟨h1, h2⟩ := h
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> revert h1 h2 <;> decide
  · obtain ⟨hlo, hhi⟩ := bounds n h5
    have hfa : 2 ≤ Nat.fib n := by
      have : Nat.fib 5 ≤ Nat.fib n := Nat.fib_mono h5
      simpa using this.trans' (by decide)
    have hc : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    obtain ⟨hta, hat⟩ := sizeWindow (Nat.fib n) hfa
    set L := Nat.size (Nat.fib n) - 2 with hL
    set t := (2 : ℕ) ^ L with htdef
    have ht1 : 0 < t := by positivity
    have e1 : (2 : ℕ) ^ (L + 1) = 2 * t := by rw [htdef]; ring
    have e2 : (2 : ℕ) ^ (L + 2) = 4 * t := by rw [htdef]; ring
    have hba := bitOf (Nat.fib n) L hta hat
    rcases Nat.eq_zero_or_pos (secondBit (Nat.fib n)) with h0 | hpos
    · have hanot : ¬ (3 * t ≤ Nat.fib n) := fun hx => by
        have := hba.mpr hx; omega
      have hb3 : 3 * t < Nat.fib (Nat.succ n) := by
        have : Nat.fib (n + 1) = Nat.fib (Nat.succ n) := rfl
        omega
      rcases Nat.lt_or_ge (Nat.fib (n + 1)) (4 * t) with hb4 | hb4
      · have hbb := bitOf (Nat.fib (n + 1)) L (by omega) hb4
        have : secondBit (Nat.fib (n + 1)) = 1 := hbb.mpr (by omega)
        omega
      · have hbhi : Nat.fib (n + 1) < 8 * t := by omega
        have hbb := bitOf (Nat.fib (n + 1)) (L + 1) (by rw [e1]; omega) (by rw [e1]; omega)
        have hcb := bitOf (Nat.fib (n + 2)) (L + 1) (by rw [e1]; omega) (by rw [e1]; omega)
        have : secondBit (Nat.fib (n + 2)) = 1 := by
          refine hcb.mpr ?_
          rw [e1]; omega
        omega
    · have ha3 : 3 * t ≤ Nat.fib n := hba.mp (by
        have : secondBit (Nat.fib n) < 2 := Nat.mod_lt _ (by norm_num)
        omega)
      have hbb := bitOf (Nat.fib (n + 1)) (L + 1) (by rw [e1]; omega) (by rw [e1]; omega)
      have hb6 : 3 * 2 ^ (L + 1) ≤ Nat.fib (n + 1) := hbb.mp (by omega)
      rw [e1] at hb6
      have hcb := bitOf (Nat.fib (n + 2)) (L + 2) (by rw [e2]; omega) (by rw [e2]; omega)
      have : secondBit (Nat.fib (n + 2)) = 0 := by
        by_contra hx
        have hlt : secondBit (Nat.fib (n + 2)) < 2 := Nat.mod_lt _ (by norm_num)
        have h1' : secondBit (Nat.fib (n + 2)) = 1 := by omega
        have := hcb.mp h1'
        rw [e2] at this
        omega
      omega

end D5.S3.Arith.FibonacciSecondBitRunLength
