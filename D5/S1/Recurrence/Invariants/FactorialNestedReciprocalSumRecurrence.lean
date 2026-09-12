/- GID: D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Data.Nat.Factorial.Basic, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Factorial-prefix updates prove Mathar's third-order recurrence for OEIS A093345. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.FactorialNestedReciprocalSumRecurrence

/-- OEIS A093345, defined over `ℚ` exactly by its factorial nested reciprocal sum. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    (1 + ∑ i ∈ Finset.Icc 1 n,
      (1 / (i : ℚ)) * ∑ j ∈ Finset.range i, 1 / (j.factorial : ℚ))

/-- Mathar's conjectured third-order recurrence for OEIS A093345, for every `n ≥ 3`.
All coefficient subtraction is in `ℚ`; subtraction in the indices is natural subtraction. -/
theorem mathar_a093345 (n : ℕ) (hn : 3 ≤ n) :
    a n - 2 * (n : ℚ) * a (n - 1) + ((n : ℚ) ^ 2 - 2) * a (n - 2) -
      ((n : ℚ) - 2) ^ 2 * a (n - 3) = 0 := by
  let b : ℕ → ℚ := fun m =>
    (m.factorial : ℚ) * ∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℚ)
  have hb (m : ℕ) : b (m + 1) = (m + 1 : ℚ) * b m + 1 := by
    dsimp [b]
    rw [Nat.factorial_succ, Finset.sum_range_succ, Nat.factorial_succ]
    push_cast
    have hfac : ((m : ℚ) + 1) * (m.factorial : ℚ) ≠ 0 := by positivity
    calc
      ((m : ℚ) + 1) * m.factorial *
            ((∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℚ)) +
              1 / (((m : ℚ) + 1) * m.factorial)) =
          ((m : ℚ) + 1) * (m.factorial *
            (∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℚ))) +
            (((m : ℚ) + 1) * m.factorial) *
              (1 / (((m : ℚ) + 1) * m.factorial)) := by ring
      _ = _ := by rw [mul_div_cancel₀ 1 hfac]
  have ha (m : ℕ) : a (m + 1) = (m + 1 : ℚ) * a m + b m := by
    rw [a, a]
    dsimp [b]
    rw [Nat.factorial_succ,
      Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)]
    push_cast
    have hsucc : (m : ℚ) + 1 ≠ 0 := by positivity
    calc
      ((m : ℚ) + 1) * m.factorial *
            (1 + ((∑ i ∈ Finset.Icc 1 m,
              1 / (i : ℚ) * ∑ j ∈ Finset.range i, 1 / (j.factorial : ℚ)) +
                1 / ((m : ℚ) + 1) *
                  ∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℚ))) =
          ((m : ℚ) + 1) *
            (m.factorial * (1 + ∑ i ∈ Finset.Icc 1 m,
              1 / (i : ℚ) * ∑ j ∈ Finset.range i, 1 / (j.factorial : ℚ))) +
            m.factorial * (((m : ℚ) + 1) * (1 / ((m : ℚ) + 1))) *
              (∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℚ)) := by ring
      _ = _ := by rw [mul_div_cancel₀ 1 hsucc]; ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have ha0 := ha m
  have ha1 := ha (m + 1)
  have ha2 := ha (m + 2)
  have hb0 := hb m
  have hb1 := hb (m + 1)
  push_cast at ha1 ha2 hb1
  have hshift :
      a (m + 3) - 2 * (m + 3 : ℚ) * a (m + 2) +
        ((m + 3 : ℚ) ^ 2 - 2) * a (m + 1) -
          ((m + 3 : ℚ) - 2) ^ 2 * a m = 0 := by
    rw [ha2, hb1, ha1, hb0, ha0]
    ring
  simpa [Nat.cast_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

#print axioms mathar_a093345

end D5.S1.Recurrence.Invariants.FactorialNestedReciprocalSumRecurrence
