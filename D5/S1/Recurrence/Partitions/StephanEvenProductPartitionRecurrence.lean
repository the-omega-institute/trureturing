/- GID: D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Basic, mathlib/module/Mathlib.Algebra.Ring.Parity, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: The maximum even product of partitions triples when the partitioned integer increases by three. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace D5.S1.Recurrence.Partitions.StephanEvenProductPartitionRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The classical maximum product of the parts of a partition (OEIS A000792). -/
def classicalMaximumProduct : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | n + 5 => 3 * classicalMaximumProduct (n + 2)

private theorem classicalMaximumProduct_add_three (n : ℕ) (hn : 2 ≤ n) :
    classicalMaximumProduct (n + 3) = 3 * classicalMaximumProduct n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k + 3 = k + 5 by omega, show 2 + k = k + 2 by omega]
  rfl

private theorem self_le_classicalMaximumProduct (n : ℕ) :
    n ≤ classicalMaximumProduct n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 5
      · interval_cases n <;> norm_num [classicalMaximumProduct]
      · have htwo : 2 ≤ n - 3 := by omega
        calc
          n = (n - 3) + 3 := by omega
          _ ≤ 3 * (n - 3) := by omega
          _ ≤ 3 * classicalMaximumProduct (n - 3) :=
            Nat.mul_le_mul_left 3 (ih (n - 3) (by omega))
          _ = classicalMaximumProduct n := by
            rw [← classicalMaximumProduct_add_three (n - 3) htwo]
            congr
            omega

private theorem classicalMaximumProduct_mul_le (a b : ℕ) :
    classicalMaximumProduct a * classicalMaximumProduct b ≤
      classicalMaximumProduct (a + b) := by
  by_cases ha : 5 ≤ a
  · have ha' : 2 ≤ a - 3 := by omega
    rw [show a = (a - 3) + 3 by omega,
      classicalMaximumProduct_add_three (a - 3) ha',
      show (a - 3) + 3 + b = ((a - 3) + b) + 3 by omega,
      classicalMaximumProduct_add_three ((a - 3) + b) (by omega)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_left 3 (classicalMaximumProduct_mul_le (a - 3) b)
  · by_cases hb : 5 ≤ b
    · have hb' : 2 ≤ b - 3 := by omega
      rw [show b = (b - 3) + 3 by omega,
        classicalMaximumProduct_add_three (b - 3) hb',
        show a + ((b - 3) + 3) = (a + (b - 3)) + 3 by omega,
        classicalMaximumProduct_add_three (a + (b - 3)) (by omega)]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        Nat.mul_le_mul_left 3 (classicalMaximumProduct_mul_le a (b - 3))
    · interval_cases a <;> interval_cases b <;> norm_num [classicalMaximumProduct]
termination_by a + b
decreasing_by all_goals omega

private theorem multisetProduct_le_classicalMaximumProduct (s : Multiset ℕ) :
    s.prod ≤ classicalMaximumProduct s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [classicalMaximumProduct]
  | @cons a s ih =>
      simp only [Multiset.prod_cons, Multiset.sum_cons]
      exact (Nat.mul_le_mul (self_le_classicalMaximumProduct a) ih).trans
        (classicalMaximumProduct_mul_le a s.sum)

private def classicalWitnessParts : ℕ → Multiset ℕ
  | 0 => 0
  | 1 => 1 ::ₘ 0
  | 2 => 2 ::ₘ 0
  | 3 => 3 ::ₘ 0
  | 4 => 2 ::ₘ 2 ::ₘ 0
  | n + 5 => 3 ::ₘ classicalWitnessParts (n + 2)

private theorem classicalWitnessParts_spec (n : ℕ) :
    (∀ x ∈ classicalWitnessParts n, 0 < x) ∧
      (classicalWitnessParts n).sum = n ∧
      (classicalWitnessParts n).prod = classicalMaximumProduct n := by
  match n with
  | 0 => simp [classicalWitnessParts, classicalMaximumProduct]
  | 1 => simp [classicalWitnessParts, classicalMaximumProduct]
  | 2 => simp [classicalWitnessParts, classicalMaximumProduct]
  | 3 => simp [classicalWitnessParts, classicalMaximumProduct]
  | 4 => simp [classicalWitnessParts, classicalMaximumProduct]
  | n + 5 =>
      rcases classicalWitnessParts_spec (n + 2) with ⟨hpos, hsum, hprod⟩
      simp only [classicalWitnessParts, classicalMaximumProduct, Multiset.mem_cons,
        Multiset.sum_cons, Multiset.prod_cons]
      exact ⟨by simpa using hpos, by omega, by rw [hprod]⟩
termination_by n

/-- A000792: the displayed value is the greatest product of the parts of a partition of `n`. -/
theorem classicalMaximumProduct_isGreatest (n : ℕ) :
    IsGreatest {q : ℕ | ∃ p : Nat.Partition n, p.parts.prod = q}
      (classicalMaximumProduct n) := by
  rcases classicalWitnessParts_spec n with ⟨hpos, hsum, hprod⟩
  let p : Nat.Partition n :=
    ⟨classicalWitnessParts n, fun {x} hx => hpos x hx, hsum⟩
  constructor
  · refine ⟨p, ?_⟩
    exact hprod
  · rintro q ⟨qpart, rfl⟩
    simpa only [qpart.parts_sum] using
      multisetProduct_le_classicalMaximumProduct qpart.parts

private def evenMaximumBound : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 6
  | 6 => 8
  | n + 7 => 3 * evenMaximumBound (n + 4)

private theorem evenMaximumBound_add_three (n : ℕ) (hn : 4 ≤ n) :
    evenMaximumBound (n + 3) = 3 * evenMaximumBound n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 4 + k + 3 = k + 7 by omega, show 4 + k = k + 4 by omega]
  rfl

private theorem nine_mul_evenMaximumBound_le_add_six (n : ℕ) (hn : 2 ≤ n) :
    9 * evenMaximumBound n ≤ evenMaximumBound (n + 6) := by
  by_cases hsmall : n < 4
  · interval_cases n <;> norm_num [evenMaximumBound]
  · rw [show n + 6 = (n + 3) + 3 by omega,
      evenMaximumBound_add_three (n + 3) (by omega),
      evenMaximumBound_add_three n (by omega)]
    omega

end D5.S1.Recurrence.Partitions.StephanEvenProductPartitionRecurrence
