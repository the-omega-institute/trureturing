/- GID: D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.balaConjecture; result=D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.bala_conjecture_false; claim=D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.balaConjecture
   digest: Secant residues at indices 1 and 19 refute pure periodicity modulo 27. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.NatFactorial

namespace D5.S1.Recurrence.Periodic.SecantNumberPurePeriodRefutation

/-! The OEIS A000364 recurrence is reindexed with j ranging over Fin (n + 1).
Its strong-induction reduction to ZMod 27 supplies a finite refutation of
Bala's pure-periodicity claim. No eventual-periodicity claim is asserted. -/

open scoped BigOperators
-- Prevent eager evaluation of the recursive choose definition during simplification.
-- Exact coefficients are computed through Mathlib's factorial identity instead.
attribute [local irreducible] Nat.choose

private def seq (R : Type*) [CommRing R] : ℕ → R
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1),
      (-1 : R) ^ (j.val + 2) * (Nat.choose (2 * (n + 1)) (2 * (j.val + 1)) : R) *
        seq R (n - j.val)
termination_by n => n

/-- Euler secant numbers, defined by the entry's integer recurrence. -/
def a : ℕ → ℤ := seq ℤ

/-- The same recurrence computed directly in the residue ring. -/
def b : ℕ → ZMod 27 := seq (ZMod 27)

/-- Reduction commutes with the recurrence at every index. -/
theorem reduction (n : ℕ) : (a n : ZMod 27) = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a, b, seq]
    | succ n =>
      change (seq ℤ (n + 1) : ZMod 27) = seq (ZMod 27) (n + 1)
      rw [seq, seq]
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (seq ℤ (n - j.val) : ZMod 27) = seq (ZMod 27) (n - j.val) from
        ih _ (by omega)]

private theorem b_zero : b 0 = 1 := by simp [b, seq]
private theorem b_succ (n : ℕ) : b (n + 1) = ∑ j : Fin (n + 1),
    (-1 : ZMod 27) ^ (j.val + 2) * (Nat.choose (2 * (n + 1)) (2 * (j.val + 1)) : ZMod 27) * b (n - j.val) := by
  exact seq.eq_2 _ _

private theorem b_one : b 1 = 1 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [b_zero]

private theorem b_2 : b 2 = 5 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one]

private theorem b_3 : b 3 = 7 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2]
  decide

private theorem b_4 : b 4 = 8 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3]
  decide

private theorem b_5 : b 5 = 4 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4]
  decide

private theorem b_6 : b 6 = 11 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5]
  decide

private theorem b_7 : b 7 = 1 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6]
  decide

private theorem b_8 : b 8 = 14 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7]
  decide

private theorem b_9 : b 9 = 25 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8]
  decide

private theorem b_10 : b 10 = 17 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9]
  decide

private theorem b_11 : b 11 = 22 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10]
  decide

private theorem b_12 : b 12 = 20 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11]
  decide

private theorem b_13 : b 13 = 19 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12]
  decide

private theorem b_14 : b 14 = 23 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12, b_13]
  decide

private theorem b_15 : b 15 = 16 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12, b_13, b_14]
  decide

private theorem b_16 : b 16 = 26 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12, b_13, b_14, b_15]
  decide

private theorem b_17 : b 17 = 13 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16]
  decide

private theorem b_18 : b 18 = 2 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17]
  decide

private theorem b_19 : b 19 = 10 := by
  rw [b_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [Nat.choose_eq_factorial_div_factorial, b_zero, b_one, b_2, b_3, b_4, b_5, b_6, b_7, b_8,
    b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18]
  decide

/-- Initial condition and the reindexed OEIS recurrence. -/
theorem a_recurrence : a 0 = 1 ∧ ∀ n : ℕ, a (n + 1) =
    ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 2) *
      (Nat.choose (2 * (n + 1)) (2 * (j.val + 1)) : ℤ) * a (n - j.val) := by
  exact ⟨seq.eq_1 _, fun n => seq.eq_2 _ n⟩

/-- Any integer sequence obeying the same initial condition and recurrence is a. -/
theorem a_unique (c : ℕ → ℤ) (hzero : c 0 = 1)
    (hstep : ∀ n : ℕ, c (n + 1) = ∑ j : Fin (n + 1),
      (-1 : ℤ) ^ (j.val + 2) * (Nat.choose (2 * (n + 1)) (2 * (j.val + 1)) : ℤ) *
        c (n - j.val)) : c = a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hzero.trans a_recurrence.1.symm
    | succ n =>
      rw [hstep, a_recurrence.2]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih _ (by omega)]

private theorem a_one : a 1 = 1 := by
  rw [a_recurrence.2]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [a_recurrence.1]
private theorem a_two : a 2 = 5 := by
  rw [a_recurrence.2]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [a_recurrence.1, a_one, Nat.choose_eq_factorial_div_factorial]

/-- The first four published DATA values. -/
theorem initial_values : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 61 := by
  refine ⟨a_recurrence.1, a_one, a_two, ?_⟩
  rw [a_recurrence.2]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul]
  norm_num [a_recurrence.1, a_one, a_two, Nat.choose_eq_factorial_div_factorial]

theorem residue_one : (a 1 : ZMod 27) = 1 := by rw [reduction, b_one]
theorem residue_nineteen : (a 19 : ZMod 27) = 10 := by rw [reduction, b_19]

/-- Bala's pure-periodicity conjecture specialized to modulus 27. -/
def balaConjecture : Prop := ∃ d : ℕ, 0 < d ∧ d ∣ Nat.totient 27 ∧
  ∀ n : ℕ, 1 ≤ n → (a (n + d) : ZMod 27) = (a n : ZMod 27)

/-- The residues at indices 1 and 19 refute pure periodicity with a period dividing phi(27). -/
theorem bala_conjecture_false : ¬ balaConjecture := by
  rintro ⟨d, hd, hdiv, hp⟩
  have ht : Nat.totient 27 = 18 := by decide
  rw [ht] at hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hperiod : Function.Periodic (fun n : ℕ => (a (n + 1) : ZMod 27)) d := by
    intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp (n + 1) (by omega)
  have h := hperiod.nat_mul m 0
  simp only [Nat.cast_id, Nat.zero_add] at h
  rw [Nat.mul_comm m d, ← hm] at h
  have heq : (10 : ZMod 27) = 1 := residue_nineteen.symm.trans (h.trans residue_one)
  exact (by decide : (10 : ZMod 27) ≠ 1) heq

#print axioms a
#print axioms b
#print axioms reduction
#print axioms a_recurrence
#print axioms a_unique
#print axioms initial_values
#print axioms residue_one
#print axioms residue_nineteen
#print axioms balaConjecture
#print axioms bala_conjecture_false

end D5.S1.Recurrence.Periodic.SecantNumberPurePeriodRefutation
