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

private theorem evenFactor_mul_classicalMaximumProduct_le
    (x y : ℕ) (hx : 0 < x) (hxeven : Even x) :
    x * classicalMaximumProduct y ≤ evenMaximumBound (x + y) := by
  have hx2 : 2 ≤ x := by
    rcases hxeven with ⟨k, hk⟩
    omega
  by_cases hy : 5 ≤ y
  · have hy2 : 2 ≤ y - 3 := by omega
    rw [show y = (y - 3) + 3 by omega,
      classicalMaximumProduct_add_three (y - 3) hy2,
      show x + ((y - 3) + 3) = (x + (y - 3)) + 3 by omega,
      evenMaximumBound_add_three (x + (y - 3)) (by omega)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_left 3
        (evenFactor_mul_classicalMaximumProduct_le x (y - 3) hx hxeven)
  · by_cases hxlarge : 8 ≤ x
    · have hxsubpos : 0 < x - 6 := by omega
      have hxsubeven : Even (x - 6) := by
        rcases hxeven with ⟨k, hk⟩
        exact ⟨k - 3, by omega⟩
      calc
        x * classicalMaximumProduct y ≤
            (9 * (x - 6)) * classicalMaximumProduct y := by
              exact Nat.mul_le_mul_right _ (by omega)
        _ = 9 * ((x - 6) * classicalMaximumProduct y) := by ac_rfl
        _ ≤ 9 * evenMaximumBound ((x - 6) + y) :=
          Nat.mul_le_mul_left 9
            (evenFactor_mul_classicalMaximumProduct_le
              (x - 6) y hxsubpos hxsubeven)
        _ ≤ evenMaximumBound (((x - 6) + y) + 6) :=
          nine_mul_evenMaximumBound_le_add_six ((x - 6) + y) (by omega)
        _ = evenMaximumBound (x + y) := by
          congr 1
          omega
    · interval_cases x <;> interval_cases y <;>
        norm_num [even_iff_two_dvd] at hxeven <;>
        norm_num [classicalMaximumProduct, evenMaximumBound]
termination_by x + y
decreasing_by all_goals omega

private theorem exists_even_mem_of_even_prod (s : Multiset ℕ) (h : Even s.prod) :
    ∃ x ∈ s, Even x := by
  induction s using Multiset.induction_on with
  | empty => norm_num [even_iff_two_dvd] at h
  | @cons a s ih =>
      by_cases ha : Even a
      · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
      · by_cases hs : Even s.prod
        · obtain ⟨x, hxs, hx⟩ := ih hs
          exact ⟨x, Multiset.mem_cons_of_mem hxs, hx⟩
        · have haodd : Odd a := Nat.not_even_iff_odd.mp ha
          have hsodd : Odd s.prod := Nat.not_even_iff_odd.mp hs
          have hodd : Odd ((a ::ₘ s).prod) := by
            simpa only [Multiset.prod_cons] using haodd.mul hsodd
          exact (Nat.not_even_iff_odd.mpr hodd h).elim

private theorem evenPartitionProduct_le_bound {n : ℕ} (p : Nat.Partition n)
    (heven : Even p.parts.prod) : p.parts.prod ≤ evenMaximumBound n := by
  obtain ⟨x, hxmem, hxeven⟩ := exists_even_mem_of_even_prod p.parts heven
  have hxpos : 0 < x := p.parts_pos hxmem
  calc
    p.parts.prod = x * (p.parts.erase x).prod := (Multiset.prod_erase hxmem).symm
    _ ≤ x * classicalMaximumProduct (p.parts.erase x).sum :=
      Nat.mul_le_mul_left x (multisetProduct_le_classicalMaximumProduct (p.parts.erase x))
    _ ≤ evenMaximumBound (x + (p.parts.erase x).sum) :=
      evenFactor_mul_classicalMaximumProduct_le x (p.parts.erase x).sum hxpos hxeven
    _ = evenMaximumBound n := by
      rw [Multiset.sum_erase hxmem, p.parts_sum]

private def evenWitnessParts : ℕ → Multiset ℕ
  | 0 => 0
  | 1 => 1 ::ₘ 0
  | 2 => 2 ::ₘ 0
  | 3 => 2 ::ₘ 1 ::ₘ 0
  | 4 => 2 ::ₘ 2 ::ₘ 0
  | 5 => 3 ::ₘ 2 ::ₘ 0
  | 6 => 2 ::ₘ 2 ::ₘ 2 ::ₘ 0
  | n + 7 => 3 ::ₘ evenWitnessParts (n + 4)

private theorem evenWitnessParts_spec (n : ℕ) (hn : 2 ≤ n) :
    (∀ x ∈ evenWitnessParts n, 0 < x) ∧
      (evenWitnessParts n).sum = n ∧
      (evenWitnessParts n).prod = evenMaximumBound n ∧
      Even (evenWitnessParts n).prod := by
  match n with
  | 0 => omega
  | 1 => omega
  | 2 => norm_num [evenWitnessParts, evenMaximumBound, even_iff_two_dvd]
  | 3 => norm_num [evenWitnessParts, evenMaximumBound, even_iff_two_dvd]
  | 4 => norm_num [evenWitnessParts, evenMaximumBound, even_iff_two_dvd]
  | 5 => norm_num [evenWitnessParts, evenMaximumBound, even_iff_two_dvd]
  | 6 => norm_num [evenWitnessParts, evenMaximumBound, even_iff_two_dvd]
  | n + 7 =>
      rcases evenWitnessParts_spec (n + 4) (by omega) with
        ⟨hpos, hsum, hprod, heven⟩
      simp only [evenWitnessParts, evenMaximumBound, Multiset.mem_cons,
        Multiset.sum_cons, Multiset.prod_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases hx with rfl | hx
        · norm_num
        · exact hpos x hx
      · omega
      · rw [hprod]
      · exact heven.mul_left 3
termination_by n

private theorem evenMaximumBound_isGreatest (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest
      {q : ℕ | ∃ p : Nat.Partition n, Even p.parts.prod ∧ p.parts.prod = q}
      (evenMaximumBound n) := by
  rcases evenWitnessParts_spec n hn with ⟨hpos, hsum, hprod, heven⟩
  let p : Nat.Partition n :=
    ⟨evenWitnessParts n, fun {x} hx => hpos x hx, hsum⟩
  constructor
  · refine ⟨p, ?_, ?_⟩
    · exact heven
    · exact hprod
  · rintro q ⟨qpart, hqeven, rfl⟩
    exact evenPartitionProduct_le_bound qpart hqeven

/-- A091915: after `n = 6`, the greatest even partition product triples at `n + 3`. -/
theorem result (n : ℕ) (hn : 6 < n) :
    ∃ a : ℕ,
      IsGreatest
          {q : ℕ | ∃ p : Nat.Partition n, Even p.parts.prod ∧ p.parts.prod = q} a ∧
        IsGreatest
          {q : ℕ | ∃ p : Nat.Partition (n + 3), Even p.parts.prod ∧ p.parts.prod = q}
          (3 * a) := by
  refine ⟨evenMaximumBound n, evenMaximumBound_isGreatest n (by omega), ?_⟩
  rw [← evenMaximumBound_add_three n (by omega)]
  exact evenMaximumBound_isGreatest (n + 3) (by omega)

end D5.S1.Recurrence.Partitions.StephanEvenProductPartitionRecurrence
