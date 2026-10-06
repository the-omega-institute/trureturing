/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Colin Barker's conjectured recurrence and generating function for OEIS A266614, the number of ON cells of the Rule 41 elementary cellular automaton started from a single ON cell. -/

/-
proof_shape: rule41, onCount: definition (Wolfram rule 41, and the number of ON cells among
  positions -n..n of its single-seed evolution on ℤ)
proof_shape: claim: definition (the two conjectured forms recorded in OEIS A266614)
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the row
  invariant `hrow` (row n differs from the background, OFF for even n and ON for odd n, exactly
  at {n}, {n - 2, n - 1, n}, {n - 2, n} or {n - 4, n - 3, n - 1, n} according as n ≡ 0, 1, 2, 3
  mod 4, by induction through the rule table) and the four counts derived from it; the
  recurrence and the coefficient comparison for the generating function are derived from them
admission_basis: open-problem-resolution (issue #13157)
Direct frozen dependencies: D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.row
  (sha256:2f10e475078d6964a1665bea58e51729cc2f6ec55df124b5a6e4b66488000833), the single-seed
  evolution on ℤ
-/

import D5.S0.Automata.RuleThirtyTwentyTwoMersenneSignRefutation
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.Rule41OnCellCount

open Finset PowerSeries
open D5.S0.Automata.RuleThirtyTwentyTwoMersenneSignRefutation (row)

/-!
OEIS A266614 (Robert Price, 2016): the number of ON (black) cells in the n-th iteration of the
"Rule 41" elementary cellular automaton started from a single ON cell. The entry's Mathematica
program evolves the whole line and counts the ON cells among the `2n + 1` central cells of row
`n`; here the evolution is the frozen single-seed row `row rule41` on ℤ. Colin Barker conjectured
a recurrence and a generating function (2016, 2019).
-/

/-- Wolfram rule 41: the new state of a cell with neighbourhood `(l, c, r)` is bit
`4l + 2c + r` of 41. -/
def rule41 (l c r : Bool) : Bool :=
  Nat.testBit 41 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- OEIS A266614: the number of ON cells among positions `-n, ..., n` of row `n` of the
automaton started from a single ON cell at the origin. -/
def onCount (n : ℕ) : ℕ :=
  ((Icc (-(n : ℤ)) n).filter fun x => row rule41 n x = true).card

/-- Barker's recurrence and generating function for A266614. The generating-function
denominator has constant term 1, so it is stated as the product of the series with the
denominator. -/
def claim : Prop :=
  (∀ n : ℕ, 5 < n →
      (onCount n : ℤ) = onCount (n - 2) + onCount (n - 4) - onCount (n - 6)) ∧
  (PowerSeries.mk (fun n => (onCount n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      1 + X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 5 * X ^ 5)

set_option maxHeartbeats 400000 in
-- The row invariant closes 32 phase-and-neighbourhood cases by `omega` within one declaration.
/-- The conjectured formulas hold. -/
theorem result : claim := by
  -- The rule table: the new cell is ON exactly for the neighbourhoods `000`, `011` and `101`.
  have hrule : ∀ l c r : Bool,
      rule41 l c r = ((!l && !c && !r) || (!l && c && r) || (l && !c && r)) := by decide
  -- Row invariant: the cells that differ from the background, which is ON in odd rows.
  have hrow : ∀ n : ℕ, ∀ x : ℤ, row rule41 n x = true ↔
      (n % 4 = 0 ∧ x = n) ∨ (n % 4 = 1 ∧ ¬ (n - 2 ≤ x ∧ x ≤ n)) ∨
        (n % 4 = 2 ∧ (x = n - 2 ∨ x = n)) ∨
        (n % 4 = 3 ∧ ¬ (x = n - 4 ∨ x = n - 3 ∨ x = n - 1 ∨ x = n)) := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [row, decide_eq_true_iff]
      constructor <;> intro h <;> omega
    | succ n ih =>
      intro x
      rw [row, hrule]
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
      have h1 := ih (x - 1)
      have h2 := ih x
      have h3 := ih (x + 1)
      have hn : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases hn with hn | hn | hn | hn <;>
      · have hn' : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
        rw [hn] at hn'
        norm_num at hn'
        simp +decide only [hn, hn', true_and, false_and, false_or, or_false] at h1 h2 h3 ⊢
        rcases Bool.eq_false_or_eq_true (row rule41 n (x - 1)) with e1 | e1 <;>
        rcases Bool.eq_false_or_eq_true (row rule41 n x) with e2 | e2 <;>
        rcases Bool.eq_false_or_eq_true (row rule41 n (x + 1)) with e3 | e3 <;>
        simp only [e1, e2, e3, true_iff, false_iff, Bool.false_eq_true, Bool.true_eq_false,
          and_true, and_false, or_true, or_false] at h1 h2 h3 ⊢ <;>
        omega
  have total : ∀ n : ℕ, ((Icc (-(n : ℤ)) n).filter fun x => row rule41 n x = true).card +
      ((Icc (-(n : ℤ)) n).filter fun x => ¬ row rule41 n x = true).card = 2 * n + 1 := by
    intro n
    rw [card_filter_add_card_filter_not]
    have hc := Int.card_Icc_of_le (-(n : ℤ)) n (by omega)
    omega
  have c0 : ∀ n : ℕ, n % 4 = 0 → onCount n = 1 := by
    intro n hn
    have hs : (Icc (-(n : ℤ)) n).filter (fun x => row rule41 n x = true) = {(n : ℤ)} := by
      ext x
      simp only [mem_filter, mem_Icc, mem_singleton, hrow]
      omega
    rw [onCount, hs, card_singleton]
  have c1 : ∀ n : ℕ, n % 4 = 1 → onCount n = 2 * n - 2 := by
    intro n hn
    have hs : (Icc (-(n : ℤ)) n).filter (fun x => ¬ row rule41 n x = true) =
        Icc ((n : ℤ) - 2) n := by
      ext x
      simp only [mem_filter, mem_Icc, hrow]
      omega
    have ht := total n
    rw [hs] at ht
    have hc := Int.card_Icc_of_le ((n : ℤ) - 2) n (by omega)
    rw [onCount]
    omega
  have c2 : ∀ n : ℕ, n % 4 = 2 → onCount n = 2 := by
    intro n hn
    have hs : (Icc (-(n : ℤ)) n).filter (fun x => row rule41 n x = true) =
        {(n : ℤ) - 2, (n : ℤ)} := by
      ext x
      simp only [mem_filter, mem_Icc, mem_insert, mem_singleton, hrow]
      omega
    rw [onCount, hs, card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
  have c3 : ∀ n : ℕ, n % 4 = 3 → onCount n = 2 * n - 3 := by
    intro n hn
    have hs : (Icc (-(n : ℤ)) n).filter (fun x => ¬ row rule41 n x = true) =
        {(n : ℤ) - 4, (n : ℤ) - 3, (n : ℤ) - 1, (n : ℤ)} := by
      ext x
      simp only [mem_filter, mem_Icc, mem_insert, mem_singleton, hrow]
      omega
    have ht := total n
    rw [hs, card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton] at ht
    rw [onCount]
    omega
  have val : ∀ n : ℕ, onCount n = if n % 4 = 0 then 1 else if n % 4 = 1 then 2 * n - 2
      else if n % 4 = 2 then 2 else 2 * n - 3 := by
    intro n
    split_ifs with h0 h1 h2
    · exact c0 n h0
    · exact c1 n h1
    · exact c2 n h2
    · exact c3 n (by omega)
  have recur : ∀ k : ℕ, (onCount (k + 6) : ℤ) =
      onCount (k + 4) + onCount (k + 2) - onCount k := by
    intro k
    rw [val (k + 6), val (k + 4), val (k + 2), val k]
    split_ifs <;> omega
  -- Coefficient comparison: the recurrence from index 6 on fixes `A · (1 - X² - X⁴ + X⁶)`.
  have gf : ∀ f : ℕ → ℤ, (∀ k, f (k + 6) = f (k + 4) + f (k + 2) - f k) →
      mk f * (1 - X ^ 2 - X ^ 4 + X ^ 6) =
        C (f 0) + C (f 1) * X + C (f 2 - f 0) * X ^ 2 + C (f 3 - f 1) * X ^ 3
          + C (f 4 - f 2 - f 0) * X ^ 4 + C (f 5 - f 3 - f 1) * X ^ 5 := by
    intro f hr
    have e : mk f * (1 - X ^ 2 - X ^ 4 + X ^ 6) =
        mk f - mk f * X ^ 2 - mk f * X ^ 4 + mk f * X ^ 6 := by
      ring
    rw [e]
    ext k
    simp only [LinearMap.map_sub, LinearMap.map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk,
      coeff_X, coeff_C]
    rcases k with _ | _ | _ | _ | _ | _ | k
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · rw [show k + 1 + 1 + 1 + 1 + 1 + 1 = k + 6 by ring]
      simp [hr]
      ring
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    simpa using recur k
  · rw [show ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) : ℤ⟦X⟧) = 1 - X ^ 2 - X ^ 4 + X ^ 6 by
        ring, gf _ recur]
    have v0 : onCount 0 = 1 := c0 0 (by norm_num)
    have v1 : onCount 1 = 0 := c1 1 (by norm_num)
    have v2 : onCount 2 = 2 := c2 2 (by norm_num)
    have v3 : onCount 3 = 3 := c3 3 (by norm_num)
    have v4 : onCount 4 = 1 := c0 4 (by norm_num)
    have v5 : onCount 5 = 8 := c1 5 (by norm_num)
    simp only [v0, v1, v2, v3, v4, v5]
    simp only [Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, map_one, map_zero, zero_mul,
      add_zero]
    norm_num
    ring

end D5.S3.StatisticalMechanics.CellularAutomata.Rule41OnCellCount
