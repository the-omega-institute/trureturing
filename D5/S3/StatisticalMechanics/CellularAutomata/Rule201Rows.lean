/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Rule201Rows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Colin Barker's 2016 recurrence and generating-function conjectures for OEIS A267681 and A267680 and M. F. Hasler's 2018 closed form for A267681: the rows of the Rule 201 elementary cellular automaton started from a single ON cell, read on the window of cells -n..n in base 2 and in base 10. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the row
  invariant `row` (for n >= 1 the cell at x is ON exactly when |x| >= 2, or x = 0 and n is even,
  by induction through the eight entries of the rule table) and the window evaluation `window`
  (the base-b value of the cells -n..n is the full geometric sum minus b^(n+1), b^(n-1) and, for
  odd n, b^n); the closed forms `closed` and `hasler`, the recurrences and the coefficient
  comparison for the generating functions are derived from these two new propositions
admission_basis: open-problem-resolution (issue #11102)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.Rule201Rows

open Finset PowerSeries

/-!
OEIS A267681 and A267680 (Robert Price, 2016): the rows of the "Rule 201" elementary cellular
automaton started from a single ON (black) cell, the n-th row read on the cells `-n, ..., n` as a
number in base 2 (A267681, "decimal representation") and as a string of decimal digits
(A267680, "binary representation"). Colin Barker conjectured the order-4 recurrences and the
generating functions in 2016 (and 2019 for A267680); M. F. Hasler conjectured the closed form of
A267681 in 2018. Rule 201 is the local update rule of the Floquet-PXP cellular automaton of
Wilkinson, Klobas, Prosen and Garrahan (2020); here it is applied synchronously to every cell.
-/

/-- Wolfram rule 201: the new state of a cell with neighbourhood `(l, c, r)` is bit
`4l + 2c + r` of 201. -/
def rule201 (l c r : Bool) : Bool :=
  Nat.testBit 201 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of the automaton started from a single ON cell at the origin; every cell of `ℤ` is
updated at every step. -/
def cell : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | n + 1, x => rule201 (cell n (x - 1)) (cell n x) (cell n (x + 1))

/-- The cells `-n, ..., n` of row `n` read as digits in base `b`, most significant first. -/
def windowValue (b n : ℕ) : ℕ :=
  ∑ j ∈ range (2 * n + 1), (cell n ((n : ℤ) - j)).toNat * b ^ j

/-- OEIS A267681: the window of row `n` read in base 2. -/
def decimalRepresentation (n : ℕ) : ℕ := windowValue 2 n

/-- OEIS A267680: the window of row `n` read as a string of decimal digits. -/
def binaryRepresentation (n : ℕ) : ℕ := windowValue 10 n

/-- Hasler's closed form and Barker's recurrence and generating function for A267681, and
Barker's recurrence and generating function for A267680. Each denominator has constant term 1,
so the generating function is stated as the product of the series with the denominator. -/
def claim : Prop :=
  (∀ n : ℕ, (decimalRepresentation n : ℤ) =
      2 * 4 ^ n - ((n % 2 : ℕ) * 2 + (if 0 < n then 1 else 0) * 5 : ℤ) * 2 ^ (n - 1) - 1) ∧
  (∀ n : ℕ, 4 < n → (decimalRepresentation n : ℤ) = 5 * decimalRepresentation (n - 1)
      - 20 * decimalRepresentation (n - 3) + 16 * decimalRepresentation (n - 4)) ∧
  (PowerSeries.mk (fun n => (decimalRepresentation n : ℤ)) *
      ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X)) =
      1 - 5 * X + 21 * X ^ 2 + 14 * X ^ 3 - 40 * X ^ 4) ∧
  (∀ n : ℕ, 4 < n → (binaryRepresentation n : ℤ) = 101 * binaryRepresentation (n - 1)
      - 10100 * binaryRepresentation (n - 3) + 10000 * binaryRepresentation (n - 4)) ∧
  (PowerSeries.mk (fun n => (binaryRepresentation n : ℤ)) *
      ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X)) =
      1 - 101 * X + 10101 * X ^ 2 + 89910 * X ^ 3 - 101000 * X ^ 4)

theorem result : claim := by
  -- For `n ≥ 1` the row is `…1 1 0 b 0 1 1…` with centre `b` ON exactly for even `n`.
  have row : ∀ m : ℕ, ∀ x : ℤ, cell (m + 1) x =
      (decide (x ≤ -2) || decide (2 ≤ x) || (decide (x = 0) && decide (m % 2 = 1))) := by
    intro m
    induction m with
    | zero =>
      intro x
      obtain h | h | h | h | h : x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x := by omega
      · simp [cell, h, show x ≠ 0 by omega, show x - 1 ≠ 0 by omega, show x + 1 ≠ 0 by omega,
          rule201]
      · subst h; decide
      · subst h; decide
      · subst h; decide
      · simp [cell, show ¬ x ≤ -2 by omega, h, show x ≠ 0 by omega, show x - 1 ≠ 0 by omega,
          show x + 1 ≠ 0 by omega, rule201]
    | succ m ih =>
      intro x
      rw [cell, ih, ih, ih]
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
      · have hm' : (m + 1) % 2 = 1 - m % 2 := by omega
        rw [hm] at hm'
        obtain h | h | h | h | h | h | h :
            x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x := by omega
        · simp +decide [show x - 1 ≤ -2 by omega, show x + 1 ≤ -2 by omega,
            show x ≤ -2 by omega, rule201]
        · subst h; simp +decide [hm, hm', rule201]
        · subst h; simp +decide [hm, hm', rule201]
        · subst h; simp +decide [hm, hm', rule201]
        · subst h; simp +decide [hm, hm', rule201]
        · subst h; simp +decide [hm, hm', rule201]
        · simp +decide [show 2 ≤ x - 1 by omega, show 2 ≤ x + 1 by omega, show 2 ≤ x by omega,
            show ¬ x - 1 ≤ -2 by omega, show ¬ x + 1 ≤ -2 by omega, show ¬ x ≤ -2 by omega,
            rule201]
  -- The zero digits of the window of row `m + 1` sit at `x = ±1` and, for odd `m + 1`, at `0`.
  have window : ∀ b m : ℕ, (windowValue b (m + 1) : ℤ) =
      (∑ j ∈ range (2 * m + 3), (b : ℤ) ^ j) - b ^ m - b ^ (m + 2)
        - (if m % 2 = 0 then (b : ℤ) ^ (m + 1) else 0) := by
    intro b m
    have digit : ∀ j ∈ range (2 * m + 3),
        (((cell (m + 1) (((m + 1 : ℕ) : ℤ) - j)).toNat * b ^ j : ℕ) : ℤ) =
          (b : ℤ) ^ j - (if j = m then (b : ℤ) ^ j else 0) - (if j = m + 2 then (b : ℤ) ^ j else 0)
            - (if j = m + 1 then (if m % 2 = 0 then (b : ℤ) ^ j else 0) else 0) := by
      intro j hj
      rw [mem_range] at hj
      rw [row]
      push_cast
      obtain h | h | h | h | h : j + 1 ≤ m ∨ j = m ∨ j = m + 1 ∨ j = m + 2 ∨ m + 3 ≤ j := by omega
      · simp [show (2 : ℤ) ≤ (m : ℤ) + 1 - j by omega, show j ≠ m by omega,
          show j ≠ m + 2 by omega, show j ≠ m + 1 by omega]
      · subst h; simp
      · subst h
        rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> simp [hm]
      · subst h; simp
      · simp [show (m : ℤ) + 1 - j ≤ -2 by omega, show j ≠ m by omega,
          show j ≠ m + 2 by omega, show j ≠ m + 1 by omega]
    rw [windowValue, Nat.cast_sum, show 2 * (m + 1) + 1 = 2 * m + 3 by ring, sum_congr rfl digit]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
      simp [sum_sub_distrib, sum_ite_eq', hm, show m < 2 * m + 3 by omega,
        show m ≤ 2 * m by omega, show m < 2 * m + 2 by omega]
  -- The window value as a combination of `b ^ (2m)`, `b ^ m`, `(-b) ^ m` and `1`.
  have closed : ∀ b m : ℕ, 2 * ((b : ℤ) - 1) * windowValue b (m + 1) =
      2 * (b : ℤ) ^ (2 * m + 3) - 2 - 2 * ((b : ℤ) - 1) * (b ^ m + b ^ (m + 2))
        - ((b : ℤ) - 1) * (b ^ (m + 1) + (-1) ^ m * b ^ (m + 1)) := by
    intro b m
    have hg := geom_sum_mul (b : ℤ) (2 * m + 3)
    have hpar : 2 * (if m % 2 = 0 then (b : ℤ) ^ (m + 1) else 0) =
        b ^ (m + 1) + (-1) ^ m * b ^ (m + 1) := by
      rcases Nat.even_or_odd m with hm | hm
      · rw [if_pos (Nat.even_iff.mp hm), hm.neg_one_pow]; ring
      · rw [if_neg (by rw [Nat.odd_iff] at hm; omega), hm.neg_one_pow]; ring
    rw [window]
    linear_combination 2 * hg - ((b : ℤ) - 1) * hpar
  have hasler : ∀ n : ℕ, (decimalRepresentation n : ℤ) =
      2 * 4 ^ n - ((n % 2 : ℕ) * 2 + (if 0 < n then 1 else 0) * 5 : ℤ) * 2 ^ (n - 1) - 1 := by
    intro n
    rcases n with _ | m
    · simp [decimalRepresentation, windowValue, cell]
    · have hg := geom_sum_mul (2 : ℤ) (2 * m + 3)
      have h4 : (4 : ℤ) ^ (m + 1) = 2 ^ (2 * m + 2) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
      rw [decimalRepresentation, window, h4, if_pos (Nat.succ_pos m), Nat.add_sub_cancel]
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm
      · rw [show (m + 1) % 2 = 1 by omega, if_pos hm]
        push_cast
        linear_combination hg
      · rw [show (m + 1) % 2 = 0 by omega, if_neg (by omega)]
        push_cast
        linear_combination hg
  have rec2 : ∀ k : ℕ, (decimalRepresentation (k + 5) : ℤ) = 5 * decimalRepresentation (k + 4)
      - 20 * decimalRepresentation (k + 2) + 16 * decimalRepresentation (k + 1) := by
    intro k
    have c5 := closed 2 (k + 4)
    have c4 := closed 2 (k + 3)
    have c2 := closed 2 (k + 1)
    have c1 := closed 2 k
    rw [show k + 4 + 1 = k + 5 by ring] at c5
    rw [show k + 3 + 1 = k + 4 by ring] at c4
    rw [show k + 1 + 1 = k + 2 by ring] at c2
    simp only [decimalRepresentation]
    push_cast at c5 c4 c2 c1
    have h : 2 * (windowValue 2 (k + 5) : ℤ) = 2 * (5 * windowValue 2 (k + 4)
        - 20 * windowValue 2 (k + 2) + 16 * windowValue 2 (k + 1)) := by
      linear_combination c5 - 5 * c4 + 20 * c2 - 16 * c1
    linarith
  have rec10 : ∀ k : ℕ, (binaryRepresentation (k + 5) : ℤ) = 101 * binaryRepresentation (k + 4)
      - 10100 * binaryRepresentation (k + 2) + 10000 * binaryRepresentation (k + 1) := by
    intro k
    have c5 := closed 10 (k + 4)
    have c4 := closed 10 (k + 3)
    have c2 := closed 10 (k + 1)
    have c1 := closed 10 k
    rw [show k + 4 + 1 = k + 5 by ring] at c5
    rw [show k + 3 + 1 = k + 4 by ring] at c4
    rw [show k + 1 + 1 = k + 2 by ring] at c2
    simp only [binaryRepresentation]
    push_cast at c5 c4 c2 c1
    have h : 18 * (windowValue 10 (k + 5) : ℤ) = 18 * (101 * windowValue 10 (k + 4)
        - 10100 * windowValue 10 (k + 2) + 10000 * windowValue 10 (k + 1)) := by
      linear_combination c5 - 101 * c4 + 10100 * c2 - 10000 * c1
    linarith
  -- Coefficient comparison: a recurrence of order 4 from index 5 on fixes `A · D` up to `X ^ 4`.
  have gf : ∀ (f : ℕ → ℤ) (c1 c3 c4 : ℤ),
      (∀ k, f (k + 5) = c1 * f (k + 4) - c3 * f (k + 2) + c4 * f (k + 1)) →
      mk f * (1 - C c1 * X + C c3 * X ^ 3 - C c4 * X ^ 4) =
        C (f 0) + C (f 1 - c1 * f 0) * X + C (f 2 - c1 * f 1) * X ^ 2
          + C (f 3 - c1 * f 2 + c3 * f 0) * X ^ 3
          + C (f 4 - c1 * f 3 + c3 * f 1 - c4 * f 0) * X ^ 4 := by
    intro f c1 c3 c4 hr
    have e : mk f * (1 - C c1 * X + C c3 * X ^ 3 - C c4 * X ^ 4) =
        mk f - C c1 * (mk f * X ^ 1) + C c3 * (mk f * X ^ 3) - C c4 * (mk f * X ^ 4) := by ring
    rw [e]
    ext k
    simp only [LinearMap.map_sub, LinearMap.map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk,
      coeff_X, coeff_C]
    rcases k with _ | _ | _ | _ | _ | k
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right,
        Nat.reduceSubDiff, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, Nat.add_eq_right,
        mul_zero, add_zero, OfNat.ofNat_ne_zero]
      rw [hr]
      ring
  have v2 : ∀ m : ℕ, m < 4 → (windowValue 2 (m + 1) : ℤ) =
      (∑ j ∈ range (2 * m + 3), (2 : ℤ) ^ j) - 2 ^ m - 2 ^ (m + 2)
        - (if m % 2 = 0 then (2 : ℤ) ^ (m + 1) else 0) := fun m _ => window 2 m
  have v10 : ∀ m : ℕ, m < 4 → (windowValue 10 (m + 1) : ℤ) =
      (∑ j ∈ range (2 * m + 3), (10 : ℤ) ^ j) - 10 ^ m - 10 ^ (m + 2)
        - (if m % 2 = 0 then (10 : ℤ) ^ (m + 1) else 0) := fun m _ => window 10 m
  have z : ∀ b : ℕ, (windowValue b 0 : ℤ) = 1 := by
    intro b; simp [windowValue, cell]
  refine ⟨hasler, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    simpa using rec2 k
  · rw [show ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) : ℤ⟦X⟧) =
        1 - C 5 * X + C 20 * X ^ 3 - C 16 * X ^ 4 by simp only [map_ofNat]; ring,
      gf _ 5 20 16 rec2]
    simp only [decimalRepresentation, z, v2 0 (by norm_num), v2 1 (by norm_num),
      v2 2 (by norm_num), v2 3 (by norm_num)]
    norm_num [sum_range_succ]
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    simpa using rec10 k
  · rw [show ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) : ℤ⟦X⟧) =
        1 - C 101 * X + C 10100 * X ^ 3 - C 10000 * X ^ 4 by simp only [map_ofNat]; ring,
      gf _ 101 10100 10000 rec10]
    simp only [binaryRepresentation, z, v10 0 (by norm_num), v10 1 (by norm_num),
      v10 2 (by norm_num), v10 3 (by norm_num)]
    norm_num [sum_range_succ]
    ring

end D5.S3.StatisticalMechanics.CellularAutomata.Rule201Rows
