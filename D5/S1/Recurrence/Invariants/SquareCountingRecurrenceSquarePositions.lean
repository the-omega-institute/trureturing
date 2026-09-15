/- GID: D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Square positions and values in Zumkeller's square-counting recurrence. -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Square positions in a square-counting recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
OEIS A097602 starts at index one.
-/

namespace D5.S1.Recurrence.Invariants.SquareCountingRecurrenceSquarePositions

private instance decidableIsSquareNat (n : ℕ) : Decidable (IsSquare n) :=
  decidable_of_iff (Nat.sqrt n * Nat.sqrt n = n) (by
    simpa only [IsSquare, eq_comm] using (Nat.exists_mul_self n).symm)

/-- OEIS A097602, totalized at index zero by the sentinel value zero. -/
def a (n : ℕ) : ℕ :=
  Nat.strongRec (motive := fun _ => ℕ) (fun n rec =>
    match n with
    | 0 => 0
    | 1 => 1
    | j + 2 =>
        rec (j + 1) (by omega) +
          ((Finset.Icc 1 (j + 1)).filter fun k =>
            IsSquare (if hk : k < j + 2 then rec k hk else 0)).card) n

private def c (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k => IsSquare (a k)).card

private theorem block_invariant (k : ℕ) :
    a (9 * k + 1) = (3 * k + 1) ^ 2 ∧
      c (9 * k + 1) = 2 * k + 1 ∧
      a (9 * k + 4) = (3 * k + 2) ^ 2 ∧
      a (9 * k + 10) = (3 * k + 4) ^ 2 ∧
      c (9 * k + 10) = 2 * k + 3 ∧
      ∀ j, j < 9 →
        (IsSquare (a (9 * k + 1 + j)) ↔ j = 0 ∨ j = 3) := by
  have a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = a n + c n := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + j = j + 1 by omega]
    change a (Nat.succ (Nat.succ j)) = a (Nat.succ j) + c (Nat.succ j)
    rw [a, Nat.strongRec_eq]
    simp only
    unfold c
    congr 1
    apply congrArg Finset.card
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hs⟩
      have hlt : q < j + 2 := by
        simp only [Finset.mem_Icc] at hq
        omega
      exact ⟨hq, by simpa [hlt, a] using hs⟩
    · rintro ⟨hq, hs⟩
      have hlt : q < j + 2 := by
        simp only [Finset.mem_Icc] at hq
        omega
      exact ⟨hq, by simpa [hlt, a] using hs⟩
  have c_step (n : ℕ) :
      c (n + 1) = c n + if IsSquare (a (n + 1)) then 1 else 0 := by
    unfold c
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc]
    by_cases hs : IsSquare (a (n + 1))
    · simp [hs, Finset.filter_insert]
    · simp [hs, Finset.filter_insert]
  have not_square_between (r x : ℕ) (hl : r ^ 2 < x) (hu : x < (r + 1) ^ 2) :
      ¬IsSquare x := by
    rintro ⟨y, rfl⟩
    by_cases hy : y ≤ r
    · have hsq : y * y ≤ r * r := Nat.mul_self_le_mul_self hy
      nlinarith [hsq]
    · have hy' : r + 1 ≤ y := by omega
      have hsq : (r + 1) * (r + 1) ≤ y * y := Nat.mul_self_le_mul_self hy'
      nlinarith [hsq]
  have extend (k : ℕ)
      (ha1 : a (9 * k + 1) = (3 * k + 1) ^ 2)
      (hc1 : c (9 * k + 1) = 2 * k + 1) :
      a (9 * k + 1) = (3 * k + 1) ^ 2 ∧
        c (9 * k + 1) = 2 * k + 1 ∧
        a (9 * k + 4) = (3 * k + 2) ^ 2 ∧
        a (9 * k + 10) = (3 * k + 4) ^ 2 ∧
        c (9 * k + 10) = 2 * k + 3 ∧
        ∀ j, j < 9 →
          (IsSquare (a (9 * k + 1 + j)) ↔ j = 0 ∨ j = 3) := by
    have hs1 : IsSquare (a (9 * k + 1)) := by
      rw [ha1]
      exact ⟨3 * k + 1, pow_two _⟩
    have ha2 : a (9 * k + 2) = (3 * k + 1) ^ 2 + (2 * k + 1) := by
      calc
        a (9 * k + 2) = a (9 * k + 1) + c (9 * k + 1) := by
          convert a_step (9 * k + 1) (by omega) using 1
        _ = (3 * k + 1) ^ 2 + (2 * k + 1) := by rw [ha1, hc1]
    have hns2 : ¬IsSquare (a (9 * k + 2)) := by
      rw [ha2]
      apply not_square_between (3 * k + 1) <;> nlinarith only [Nat.zero_le k]
    have hc2 : c (9 * k + 2) = 2 * k + 1 := by
      calc
        c (9 * k + 2) = c (9 * k + 1) +
            if IsSquare (a (9 * k + 2)) then 1 else 0 := by
          convert c_step (9 * k + 1) using 1
        _ = 2 * k + 1 := by rw [hc1, if_neg hns2]
    have ha3 : a (9 * k + 3) = (3 * k + 1) ^ 2 + 2 * (2 * k + 1) := by
      calc
        a (9 * k + 3) = a (9 * k + 2) + c (9 * k + 2) := by
          convert a_step (9 * k + 2) (by omega) using 1
        _ = (3 * k + 1) ^ 2 + 2 * (2 * k + 1) := by rw [ha2, hc2]; ring
    have hns3 : ¬IsSquare (a (9 * k + 3)) := by
      rw [ha3]
      apply not_square_between (3 * k + 1) <;> nlinarith only [Nat.zero_le k]
    have hc3 : c (9 * k + 3) = 2 * k + 1 := by
      calc
        c (9 * k + 3) = c (9 * k + 2) +
            if IsSquare (a (9 * k + 3)) then 1 else 0 := by
          convert c_step (9 * k + 2) using 1
        _ = 2 * k + 1 := by rw [hc2, if_neg hns3]
    have ha4 : a (9 * k + 4) = (3 * k + 2) ^ 2 := by
      calc
        a (9 * k + 4) = a (9 * k + 3) + c (9 * k + 3) := by
          convert a_step (9 * k + 3) (by omega) using 1
        _ = (3 * k + 2) ^ 2 := by rw [ha3, hc3]; ring
    have hs4 : IsSquare (a (9 * k + 4)) := by
      rw [ha4]
      exact ⟨3 * k + 2, pow_two _⟩
    have hc4 : c (9 * k + 4) = 2 * k + 2 := by
      calc
        c (9 * k + 4) = c (9 * k + 3) +
            if IsSquare (a (9 * k + 4)) then 1 else 0 := by
          convert c_step (9 * k + 3) using 1
        _ = 2 * k + 2 := by rw [hc3, if_pos hs4]
    have ha5 : a (9 * k + 5) = (3 * k + 2) ^ 2 + (2 * k + 2) := by
      calc
        a (9 * k + 5) = a (9 * k + 4) + c (9 * k + 4) := by
          convert a_step (9 * k + 4) (by omega) using 1
        _ = (3 * k + 2) ^ 2 + (2 * k + 2) := by rw [ha4, hc4]
    have hns5 : ¬IsSquare (a (9 * k + 5)) := by
      rw [ha5]
      apply not_square_between (3 * k + 2) <;> nlinarith only [Nat.zero_le k]
    have hc5 : c (9 * k + 5) = 2 * k + 2 := by
      calc
        c (9 * k + 5) = c (9 * k + 4) +
            if IsSquare (a (9 * k + 5)) then 1 else 0 := by
          convert c_step (9 * k + 4) using 1
        _ = 2 * k + 2 := by rw [hc4, if_neg hns5]
    have ha6 : a (9 * k + 6) = (3 * k + 2) ^ 2 + 2 * (2 * k + 2) := by
      calc
        a (9 * k + 6) = a (9 * k + 5) + c (9 * k + 5) := by
          convert a_step (9 * k + 5) (by omega) using 1
        _ = (3 * k + 2) ^ 2 + 2 * (2 * k + 2) := by rw [ha5, hc5]; ring
    have hns6 : ¬IsSquare (a (9 * k + 6)) := by
      rw [ha6]
      apply not_square_between (3 * k + 2) <;> nlinarith only [Nat.zero_le k]
    have hc6 : c (9 * k + 6) = 2 * k + 2 := by
      calc
        c (9 * k + 6) = c (9 * k + 5) +
            if IsSquare (a (9 * k + 6)) then 1 else 0 := by
          convert c_step (9 * k + 5) using 1
        _ = 2 * k + 2 := by rw [hc5, if_neg hns6]
    have ha7 : a (9 * k + 7) = (3 * k + 2) ^ 2 + 3 * (2 * k + 2) := by
      calc
        a (9 * k + 7) = a (9 * k + 6) + c (9 * k + 6) := by
          convert a_step (9 * k + 6) (by omega) using 1
        _ = (3 * k + 2) ^ 2 + 3 * (2 * k + 2) := by rw [ha6, hc6]; ring
    have hns7 : ¬IsSquare (a (9 * k + 7)) := by
      rw [ha7]
      apply not_square_between (3 * k + 3) <;> nlinarith only [Nat.zero_le k]
    have hc7 : c (9 * k + 7) = 2 * k + 2 := by
      calc
        c (9 * k + 7) = c (9 * k + 6) +
            if IsSquare (a (9 * k + 7)) then 1 else 0 := by
          convert c_step (9 * k + 6) using 1
        _ = 2 * k + 2 := by rw [hc6, if_neg hns7]
    have ha8 : a (9 * k + 8) = (3 * k + 2) ^ 2 + 4 * (2 * k + 2) := by
      calc
        a (9 * k + 8) = a (9 * k + 7) + c (9 * k + 7) := by
          convert a_step (9 * k + 7) (by omega) using 1
        _ = (3 * k + 2) ^ 2 + 4 * (2 * k + 2) := by rw [ha7, hc7]; ring
    have hns8 : ¬IsSquare (a (9 * k + 8)) := by
      rw [ha8]
      apply not_square_between (3 * k + 3) <;> nlinarith only [Nat.zero_le k]
    have hc8 : c (9 * k + 8) = 2 * k + 2 := by
      calc
        c (9 * k + 8) = c (9 * k + 7) +
            if IsSquare (a (9 * k + 8)) then 1 else 0 := by
          convert c_step (9 * k + 7) using 1
        _ = 2 * k + 2 := by rw [hc7, if_neg hns8]
    have ha9 : a (9 * k + 9) = (3 * k + 2) ^ 2 + 5 * (2 * k + 2) := by
      calc
        a (9 * k + 9) = a (9 * k + 8) + c (9 * k + 8) := by
          convert a_step (9 * k + 8) (by omega) using 1
        _ = (3 * k + 2) ^ 2 + 5 * (2 * k + 2) := by rw [ha8, hc8]; ring
    have hns9 : ¬IsSquare (a (9 * k + 9)) := by
      rw [ha9]
      apply not_square_between (3 * k + 3) <;> nlinarith only [Nat.zero_le k]
    have hc9 : c (9 * k + 9) = 2 * k + 2 := by
      calc
        c (9 * k + 9) = c (9 * k + 8) +
            if IsSquare (a (9 * k + 9)) then 1 else 0 := by
          convert c_step (9 * k + 8) using 1
        _ = 2 * k + 2 := by rw [hc8, if_neg hns9]
    have ha10 : a (9 * k + 10) = (3 * k + 4) ^ 2 := by
      calc
        a (9 * k + 10) = a (9 * k + 9) + c (9 * k + 9) := by
          convert a_step (9 * k + 9) (by omega) using 1
        _ = (3 * k + 4) ^ 2 := by rw [ha9, hc9]; ring
    have hs10 : IsSquare (a (9 * k + 10)) := by
      rw [ha10]
      exact ⟨3 * k + 4, pow_two _⟩
    have hc10 : c (9 * k + 10) = 2 * k + 3 := by
      calc
        c (9 * k + 10) = c (9 * k + 9) +
            if IsSquare (a (9 * k + 10)) then 1 else 0 := by
          convert c_step (9 * k + 9) using 1
        _ = 2 * k + 3 := by rw [hc9, if_pos hs10]
    refine ⟨ha1, hc1, ha4, ha10, hc10, ?_⟩
    intro j hj
    have hj_cases :
        j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
          j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases hj_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using (iff_true_intro hs1)
    · rw [show 9 * k + 1 + 1 = 9 * k + 2 by omega]
      simp [hns2]
    · rw [show 9 * k + 1 + 2 = 9 * k + 3 by omega]
      simp [hns3]
    · rw [show 9 * k + 1 + 3 = 9 * k + 4 by omega]
      simp [hs4]
    · rw [show 9 * k + 1 + 4 = 9 * k + 5 by omega]
      simp [hns5]
    · rw [show 9 * k + 1 + 5 = 9 * k + 6 by omega]
      simp [hns6]
    · rw [show 9 * k + 1 + 6 = 9 * k + 7 by omega]
      simp [hns7]
    · rw [show 9 * k + 1 + 7 = 9 * k + 8 by omega]
      simp [hns8]
    · rw [show 9 * k + 1 + 8 = 9 * k + 9 by omega]
      simp [hns9]
  induction k with
  | zero =>
      apply extend 0
      · norm_num [a, Nat.strongRec_eq]
      · have ha : a 1 = 1 := by norm_num [a, Nat.strongRec_eq]
        unfold c
        rw [show Finset.Icc 1 1 = {1} by
          ext q
          simp only [Finset.mem_Icc, Finset.mem_singleton]
          omega]
        rw [Finset.filter_eq_self.2]
        · simp
        · intro q hq
          have hq' : q = 1 := Finset.mem_singleton.mp hq
          subst q
          rw [ha]
          exact ⟨1, by norm_num⟩
  | succ k ih =>
      apply extend (k + 1)
      · simpa only [show 9 * (k + 1) + 1 = 9 * k + 10 by ring,
            show 3 * (k + 1) + 1 = 3 * k + 4 by ring] using ih.2.2.2.1
      · simpa only [show 9 * (k + 1) + 1 = 9 * k + 10 by ring,
            show 2 * (k + 1) + 1 = 2 * k + 3 by ring] using ih.2.2.2.2.1

/-- The terms of A097602 are squares exactly at indices congruent to one or four modulo nine. -/
theorem jovovic_a097602_positions : ∀ n : ℕ, 1 ≤ n →
    (IsSquare (a n) ↔ n % 9 = 1 ∨ n % 9 = 4) := by
  intro n hn
  let k := (n - 1) / 9
  let j := (n - 1) % 9
  have hj : j < 9 := Nat.mod_lt _ (by omega)
  have hn_repr : n = 9 * k + 1 + j := by
    dsimp only [k, j]
    have hdiv := Nat.mod_add_div (n - 1) 9
    omega
  rw [hn_repr]
  rw [(block_invariant k).2.2.2.2.2 j hj]
  omega

/-- The square values occurring in A097602 are exactly `m ^ 2` with `m` not divisible by three. -/
theorem zumkeller_a097602 : ∀ m : ℕ, 1 ≤ m →
    ((∃ n, 1 ≤ n ∧ a n = m ^ 2) ↔ m % 3 ≠ 0) := by
  intro m _
  constructor
  · rintro ⟨n, hn, han⟩
    have hsq : IsSquare (a n) := by
      rw [han]
      exact ⟨m, pow_two _⟩
    rcases (jovovic_a097602_positions n hn).1 hsq with hpos | hpos
    · let k := n / 9
      have hn_repr : n = 9 * k + 1 := by
        dsimp only [k]
        have hdiv := Nat.mod_add_div n 9
        omega
      rw [hn_repr] at han
      have hm : 3 * k + 1 = m :=
        Nat.pow_left_injective (by omega) ((block_invariant k).1.symm.trans han)
      rw [← hm]
      omega
    · let k := n / 9
      have hn_repr : n = 9 * k + 4 := by
        dsimp only [k]
        have hdiv := Nat.mod_add_div n 9
        omega
      rw [hn_repr] at han
      have hm : 3 * k + 2 = m :=
        Nat.pow_left_injective (by omega) ((block_invariant k).2.2.1.symm.trans han)
      rw [← hm]
      omega
  · intro hm
    have hrem_lt : m % 3 < 3 := Nat.mod_lt _ (by omega)
    have hrem_cases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hrem_cases with hzero | hone | htwo
    · exact (hm hzero).elim
    · let k := m / 3
      have hm_repr : m = 3 * k + 1 := by
        dsimp only [k]
        have hdiv := Nat.mod_add_div m 3
        omega
      refine ⟨9 * k + 1, by omega, ?_⟩
      rw [(block_invariant k).1, hm_repr]
    · let k := m / 3
      have hm_repr : m = 3 * k + 2 := by
        dsimp only [k]
        have hdiv := Nat.mod_add_div m 3
        omega
      refine ⟨9 * k + 4, by omega, ?_⟩
      rw [(block_invariant k).2.2.1, hm_repr]

#print axioms jovovic_a097602_positions
#print axioms zumkeller_a097602

end D5.S1.Recurrence.Invariants.SquareCountingRecurrenceSquarePositions
