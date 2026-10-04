/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Colin Barker's and Ctibor O. Zizka's conjectured formulas for OEIS A266981, the number of ON cells of the Rule 79 elementary cellular automaton started from a single ON cell. -/

/-
proof_shape: rule79, cell, onCount: definition (Wolfram rule 79, its evolution on ℤ from a
  single ON cell, and the number of ON cells among positions -n..n)
proof_shape: claim: definition (the four conjectured forms recorded in OEIS A266981)
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the row
  invariant `row` (row 2k is ON exactly at the even x with 0 ≤ x ≤ 2k, and row 2k + 1 is OFF
  exactly at the odd x with 1 ≤ x ≤ 2k + 1, by induction through the rule table) and the counts
  `even` and `odd` of these two sets; the closed form, the recurrence and the coefficient
  comparison for the generating function are derived from them
admission_basis: open-problem-resolution (issue #13155)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.Rule79OnCellCount

open Finset PowerSeries

/-!
OEIS A266981 (Robert Price, 2016): the number of ON (black) cells in the n-th iteration of the
"Rule 79" elementary cellular automaton started from a single ON cell. The entry's Mathematica
program evolves the whole line and counts the ON cells among the `2n + 1` central cells of row
`n`. Colin Barker conjectured a closed form, a recurrence and a generating function (2016, 2019);
Ctibor O. Zizka conjectured the parity formulas (2025).
-/

/-- Wolfram rule 79: the new state of a cell with neighbourhood `(l, c, r)` is bit
`4l + 2c + r` of 79. -/
def rule79 (l c r : Bool) : Bool :=
  Nat.testBit 79 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of the automaton started from a single ON cell at the origin; every cell of `ℤ` is
updated at every step. -/
def cell : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | n + 1, x => rule79 (cell n (x - 1)) (cell n x) (cell n (x + 1))

/-- OEIS A266981: the number of ON cells among positions `-n, ..., n` of row `n`. -/
def onCount (n : ℕ) : ℕ :=
  ((Icc (-(n : ℤ)) n).filter fun x => cell n x = true).card

/-- Barker's closed form, recurrence and generating function, and Zizka's parity formulas, for
A266981. The generating-function denominator has constant term 1, so it is stated as the product
of the series with the denominator. -/
def claim : Prop :=
  (∀ n : ℕ, (onCount n : ℚ) = (3 + (-1) ^ n - 2 * (-2 + (-1) ^ n) * n) / 4) ∧
  (∀ n : ℕ, 3 < n → (onCount n : ℤ) = 2 * onCount (n - 2) - onCount (n - 4)) ∧
  (PowerSeries.mk (fun n => (onCount n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      1 + 2 * X + X ^ 3) ∧
  (∀ n : ℕ, onCount (2 * n) = n + 1) ∧
  (∀ n : ℕ, onCount (2 * n + 1) = 3 * n + 2)

/-- The conjectured formulas hold. -/
theorem result : claim := by
  -- The rule table: the new cell is ON exactly when `l` is OFF, or `c` is ON and `r` is OFF.
  have hrule : ∀ l c r : Bool, rule79 l c r = (!l || (c && !r)) := by decide
  -- Row invariant.
  have row : ∀ n : ℕ, ∀ x : ℤ, cell n x = true ↔
      (n % 2 = 0 ∧ 0 ≤ x ∧ x ≤ n ∧ x % 2 = 0) ∨
        (n % 2 = 1 ∧ ¬ (1 ≤ x ∧ x ≤ n ∧ x % 2 = 1)) := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [cell, decide_eq_true_iff]
      constructor <;> intro h <;> omega
    | succ n ih =>
      intro x
      rw [cell, hrule]
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
      have h1 := ih (x - 1)
      have h2 := ih x
      have h3 := ih (x + 1)
      rcases Bool.eq_false_or_eq_true (cell n (x - 1)) with e1 | e1 <;>
      rcases Bool.eq_false_or_eq_true (cell n x) with e2 | e2 <;>
      rcases Bool.eq_false_or_eq_true (cell n (x + 1)) with e3 | e3 <;>
      simp only [e1, e2, e3, true_iff, false_iff, Bool.false_eq_true, Bool.true_eq_false,
        and_true, and_false, or_true, or_false] at h1 h2 h3 ⊢ <;>
      omega
  -- Row `2k` has exactly the ON cells `0, 2, ..., 2k`.
  have even : ∀ k : ℕ, onCount (2 * k) = k + 1 := by
    intro k
    have hs : (Icc (-((2 * k : ℕ) : ℤ)) ((2 * k : ℕ) : ℤ)).filter
        (fun x => cell (2 * k) x = true) = (range (k + 1)).image (fun i : ℕ => 2 * (i : ℤ)) := by
      ext x
      simp only [mem_filter, mem_Icc, mem_image, mem_range, row]
      constructor
      · rintro ⟨-, ⟨-, h0, h1, h2⟩ | ⟨h, -⟩⟩
        · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
          exact ⟨i / 2, by omega, by omega⟩
        · omega
      · rintro ⟨i, hi, rfl⟩
        omega
    rw [onCount, hs, card_image_of_injective _ (by intro a b h; simp only at h; omega),
      card_range]
  -- Row `2k + 1` has exactly the OFF cells `1, 3, ..., 2k + 1` inside the window.
  have odd : ∀ k : ℕ, onCount (2 * k + 1) = 3 * k + 2 := by
    intro k
    have hs : (Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ)).filter
        (fun x => ¬ cell (2 * k + 1) x = true) =
          (range (k + 1)).image (fun i : ℕ => 2 * (i : ℤ) + 1) := by
      ext x
      simp only [mem_filter, mem_Icc, mem_image, mem_range, row]
      constructor
      · rintro ⟨⟨hl, hu⟩, h⟩
        have hx : 1 ≤ x := by omega
        obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = (x - 1) / 2 :=
          ⟨((x - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
        exact ⟨i, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    have htot := card_filter_add_card_filter_not
      (s := Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ))
      (fun x => cell (2 * k + 1) x = true)
    rw [hs, card_image_of_injective _ (by intro a b h; simp only at h; omega), card_range]
      at htot
    have hc := Int.card_Icc_of_le (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ) (by omega)
    rw [onCount]
    omega
  have val : ∀ n : ℕ, onCount n = if n % 2 = 0 then n / 2 + 1 else 3 * (n / 2) + 2 := by
    intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [even, if_pos (by omega)]; omega
    · rw [odd, if_neg (by omega)]; omega
  have recur : ∀ k : ℕ, (onCount (k + 4) : ℤ) = 2 * onCount (k + 2) - onCount k := by
    intro k
    rw [val (k + 4), val (k + 2), val k]
    split_ifs <;> omega
  -- Coefficient comparison: the recurrence from index 4 on fixes `A · (1 - 2X² + X⁴)`.
  have gf : ∀ f : ℕ → ℤ, (∀ k, f (k + 4) = 2 * f (k + 2) - f k) →
      mk f * (1 - C 2 * X ^ 2 + X ^ 4) =
        C (f 0) + C (f 1) * X + C (f 2 - 2 * f 0) * X ^ 2 + C (f 3 - 2 * f 1) * X ^ 3 := by
    intro f hr
    have e : mk f * (1 - C 2 * X ^ 2 + X ^ 4) = mk f - C 2 * (mk f * X ^ 2) + mk f * X ^ 4 := by
      ring
    rw [e]
    ext k
    simp only [LinearMap.map_sub, LinearMap.map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk,
      coeff_X, coeff_C]
    rcases k with _ | _ | _ | _ | k
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · rw [show k + 1 + 1 + 1 + 1 = k + 4 by ring]
      simp [hr]
  refine ⟨?_, ?_, ?_, even, odd⟩
  · intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [even]; push_cast; rw [pow_mul, neg_one_sq, one_pow]; ring
    · rw [odd]; push_cast; rw [pow_succ, pow_mul, neg_one_sq, one_pow]; ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simpa using recur k
  · rw [show ((1 - X) ^ 2 * (1 + X) ^ 2 : ℤ⟦X⟧) = 1 - C 2 * X ^ 2 + X ^ 4 by
        simp only [map_ofNat]; ring, gf _ recur]
    have v0 : onCount 0 = 1 := by simpa using even 0
    have v1 : onCount 1 = 2 := by simpa using odd 0
    have v2 : onCount 2 = 2 := by simpa using even 1
    have v3 : onCount 3 = 5 := by simpa using odd 1
    simp only [v0, v1, v2, v3]
    simp only [Nat.cast_one, Nat.cast_ofNat, map_one, mul_one, sub_self, map_zero,
      zero_mul, add_zero]
    norm_num

end D5.S3.StatisticalMechanics.CellularAutomata.Rule79OnCellCount
