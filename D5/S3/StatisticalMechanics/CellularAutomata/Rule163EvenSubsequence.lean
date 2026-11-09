/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves the OEIS A392003 even-subsequence and A266753 Rule 163 conjectures. -/

/-
proof_shape: rule163, A, B, claim, word: definition.
proof_shape: rule_table: bind-only; consumers: word_step, row_word.
proof_shape: word_step: bind-only; consumer: row_word.
proof_shape: row_word: content; escape_witness: row_word; consumer: A_succ.
proof_shape: A_succ: content; escape_witness: row_word; consumers: A_scaled, A_recurrence, generating_identity.
proof_shape: A_zero: bind-only; consumer: generating_identity.
proof_shape: A_one: bind-only; consumers: A_scaled, generating_identity.
proof_shape: A_scaled: content; escape_witness: row_word; consumer: A_closed.
proof_shape: A_closed: content; escape_witness: row_word; consumer: result.
proof_shape: A_recurrence: content; escape_witness: row_word; consumers: A_second, result.
proof_shape: A_second: content; escape_witness: row_word; consumers: generating_identity, result.
proof_shape: generating_identity: content; escape_witness: row_word; consumer: result.
proof_shape: result: content; escape_witness: row_word (same-module helpers expanded).
escape_witness: row_word, the complete integer-lattice positive-time row invariant.
No escape-witness admission basis is requested; admission uses the external open-problem resolution.
admission_basis: open-problem-resolution (#22909; Proved)
Direct frozen dependencies: D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.row
  (declaration statement_id sha256:2f10e475078d6964a1665bea58e51729cc2f6ec55df124b5a6e4b66488000833).
  Its generated equation row.eq_2 has declaration statement_id
  sha256:b00359aab1a413b7dd85891d263f56ca2c54ee1fbb7b8c85aaba1b524ce0af98.
The rule and sequences use the source expressions; the integer-lattice evolution uses
its existing owner. The positive-time row invariant includes the all-one exterior.
Utility none: the conclusions concern every time and a formal power series; finite
rule-table and initial-value evaluations are consumed steps of the induction.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27131.
-/

import D5.S0.Automata.RuleThirtyTwentyTwoMersenneSignRefutation
import Mathlib.RingTheory.PowerSeries.Basic


set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.Rule163EvenSubsequence

open Finset PowerSeries
open D5.S0.Automata.RuleThirtyTwentyTwoMersenneSignRefutation (row)

/-- Wolfram rule 163: bit 4*l + 2*c + r of 163. -/
def rule163 (l c r : Bool) : Bool :=
  Nat.testBit 163 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- A266753: cells -n,...,n of the full integer-lattice evolution,
read from left to right as a binary integer (rightmost bit has weight 1). -/
def A (n : ℕ) : ℕ :=
  ∑ j ∈ range (2 * n + 1), (row rule163 n ((n : ℤ) - j)).toNat * 2 ^ j

/-- A392003 NAME, used on its source domain m >= 1. -/
def B (m : ℕ) : ℚ :=
  (7 * (2 : ℚ) ^ m - 9 + 5 * (-1 : ℚ) ^ m) / 6

/-- Hofmann's entire subsequence conjecture; Barker's empirical formula,
recurrence and generating function; and Yurramendi's first-order recurrence.
The generating series is constructed from the explicitly defined evolution.
Its equation is a product identity in Z[[X]], so no analytic convergence
or choice of an implicitly characterized sequence is assumed. -/
def claim : Prop :=
  (∀ n : ℕ, 1 ≤ n → B (2 * n) = (A n : ℚ)) ∧
  (∀ n : ℕ, 1 < n → (A n : ℚ) = (7 * (4 : ℚ) ^ n - 4) / 6) ∧
  (∀ n : ℕ, 1 < n → A n = 4 * A (n - 1) + 2) ∧
  (∀ n : ℕ, 2 < n → (A n : ℤ) = 5 * (A (n - 1) : ℤ) - 4 * (A (n - 2) : ℤ)) ∧
  (PowerSeries.mk (fun n : ℕ => (A n : ℤ)) * ((1 - X) * (1 - 4 * X)) =
    1 - X + 2 * X ^ 2)


private def word (n : ℕ) (j : ℤ) : Bool :=
  decide (j < 0 ∨ 2 * (n : ℤ) < j ∨ j = 0 ∨ (3 ≤ j ∧ j % 2 = 1))

private theorem rule_table (l c r : Bool) :
    rule163 l c r = ((!l && !c) || (l && r)) := by
  cases l <;> cases c <;> cases r <;> decide

private theorem word_step (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    rule163 (word n (j - 2)) (word n (j - 1)) (word n j) = word (n + 1) j := by
  apply Bool.eq_iff_iff.mpr
  simp only [rule_table, word, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  push_cast
  omega

private theorem row_word (n : ℕ) (hn : 1 ≤ n) (r : ℤ) :
    row rule163 n r = word n (r + n) := by
  induction n, hn using Nat.le_induction generalizing r
  case base =>
    apply Bool.eq_iff_iff.mpr
    simp only [row, rule_table, word, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    norm_num
    omega
  case succ n hn ih =>
    rw [row, ih (r - 1), ih r, ih (r + 1)]
    convert word_step n hn (r + (n + 1 : ℕ)) using 1
    all_goals congr 2 <;> push_cast <;> ring

private theorem A_succ (n : ℕ) (hn : 1 ≤ n) : A (n + 1) = 4 * A n + 2 := by
  have h0 : row rule163 (n + 1) (n + 1) = false := by
    rw [row_word (n + 1) (by omega)]
    simp only [word, decide_eq_false_iff_not]
    push_cast
    omega
  have h1 : row rule163 (n + 1) (n : ℤ) = true := by
    rw [row_word (n + 1) (by omega)]
    simp only [word, decide_eq_true_eq]
    push_cast
    omega
  have hshift (j : ℕ) (hj : j < 2 * n + 1) :
      row rule163 (n + 1) (((n + 1 : ℕ) : ℤ) - (j + 2 : ℕ)) =
        row rule163 n ((n : ℤ) - j) := by
    rw [row_word (n + 1) (by omega), row_word n hn]
    apply Bool.eq_iff_iff.mpr
    simp only [word, decide_eq_true_eq]
    push_cast
    omega
  unfold A
  rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega, sum_range_add]
  have hlow :
      (∑ j ∈ range 2, (row rule163 (n + 1) (((n + 1 : ℕ) : ℤ) - j)).toNat * 2 ^ j) = 2 := by
    norm_num [sum_range_succ, h0, h1]
  rw [hlow]
  have hsum :
      (∑ j ∈ range (2 * n + 1),
        (row rule163 (n + 1) (((n + 1 : ℕ) : ℤ) - (2 + j : ℕ))).toNat * 2 ^ (2 + j)) =
      4 * ∑ j ∈ range (2 * n + 1),
        (row rule163 n ((n : ℤ) - j)).toNat * 2 ^ j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [show 2 + j = j + 2 by omega, hshift j (mem_range.mp hj), pow_add]
    ring
  rw [hsum]
  omega

private theorem A_zero : A 0 = 1 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

private theorem A_one : A 1 = 4 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

private theorem A_scaled (n : ℕ) (hn : 1 ≤ n) : 6 * A n + 4 = 7 * 4 ^ n := by
  induction n, hn using Nat.le_induction
  case base => norm_num [A_one]
  case succ n hn ih =>
    rw [A_succ n hn, pow_succ]
    nlinarith

private theorem A_closed (n : ℕ) (hn : 1 ≤ n) :
    (A n : ℚ) = (7 * (4 : ℚ) ^ n - 4) / 6 := by
  have h : 6 * (A n : ℚ) + 4 = 7 * (4 : ℚ) ^ n := by
    exact_mod_cast A_scaled n hn
  linarith

private theorem A_recurrence (n : ℕ) (hn : 1 < n) : A n = 4 * A (n - 1) + 2 := by
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using A_succ (n - 1) (by omega)

private theorem A_second (n : ℕ) (hn : 2 < n) :
    (A n : ℤ) = 5 * (A (n - 1) : ℤ) - 4 * (A (n - 2) : ℤ) := by
  have h1 : (A n : ℤ) = 4 * (A (n - 1) : ℤ) + 2 := by
    exact_mod_cast A_recurrence n (by omega)
  have h2 : (A (n - 1) : ℤ) = 4 * (A (n - 2) : ℤ) + 2 := by
    have h := A_recurrence (n - 1) (by omega)
    rw [show n - 1 - 1 = n - 2 by omega] at h
    exact_mod_cast h
  omega

private theorem generating_identity :
    PowerSeries.mk (fun n : ℕ => (A n : ℤ)) * ((1 - X) * (1 - 4 * X)) =
      1 - X + 2 * X ^ 2 := by
  let G : PowerSeries ℤ := PowerSeries.mk (fun n : ℕ => (A n : ℤ))
  change G * ((1 - X) * (1 - 4 * X)) = _
  rw [show G * ((1 - X) * (1 - 4 * X)) =
    G - (G * X) * 5 + (G * X ^ 2) * 4 by ring]
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | _ | n
  · norm_num [G, A_zero, coeff_mul_X_pow']
  · norm_num [G, A_zero, A_one, coeff_mul_X_pow']
  · norm_num [G, A_zero, A_one, A_succ 1 (by omega), coeff_mul_X_pow', coeff_X]
  · have h := A_second (n + 3) (by omega)
    rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] at h
    simp only [map_add, map_sub, coeff_mul_ofNat, coeff_ofNat_mul, coeff_succ_mul_X,
      coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X, coeff_X_pow, G]
    simp only [show 2 ≤ n + 3 by omega, ite_true,
      show n + 3 ≠ 0 by omega, show n + 3 ≠ 1 by omega,
      show n + 3 ≠ 2 by omega, ite_false]
    simpa using (by linarith :
      (A (n + 3) : ℤ) - (A (n + 2) : ℤ) * 5 + (A (n + 1) : ℤ) * 4 = 0)

theorem result : claim := by
  refine ⟨?_, ?_, A_recurrence, A_second, generating_identity⟩
  · intro n hn
    rw [A_closed n hn]
    unfold B
    rw [pow_mul, pow_mul]
    norm_num; ring
  · intro n hn
    exact A_closed n (by omega)

end D5.S3.StatisticalMechanics.CellularAutomata.Rule163EvenSubsequence
