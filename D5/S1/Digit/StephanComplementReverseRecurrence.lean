/- GID: D5/S1/Digit/StephanComplementReverseRecurrence
   generality: G
   mirror-B: D5/B/S1/Digit/StephanComplementReverseRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Stephan's binary complement-reversal recurrences and digit-count identities hold. -/

import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.StephanComplementReverseRecurrence

/-- OEIS A059894: complement and reverse all but the most significant bit. -/
def a (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (((Nat.digits 2 n).dropLast.reverse.map (fun d => 1 - d)) ++ [1])

/-- OEIS A054429: complement all but the most significant bit, without reversal. -/
def complementRest (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (((Nat.digits 2 n).dropLast.map (fun d => 1 - d)) ++ [1])

/-- Ralf Stephan's recurrence and digit-count conjectures from OEIS A059894. -/
theorem result :
    a 1 = 1 ∧
    (∀ n : ℕ, 0 < n → a (2 * n) = a n + 2 ^ (Nat.log 2 n + 1)) ∧
    (∀ n : ℕ, 0 < n → a (2 * n + 1) = a n + 2 ^ (Nat.log 2 n)) ∧
    (∀ n : ℕ, 0 < n →
      (Nat.digits 2 (a n)).count 1 = (Nat.digits 2 (complementRest n)).count 1 ∧
      (Nat.digits 2 (a n)).count 1 = (Nat.digits 2 n).count 0 + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [a, Nat.digits_of_lt]
  · intro n hn
    have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlen := Nat.length_digits 2 n (by decide) (by omega)
    simp only [a, Nat.digits_base_mul (b := 2) (by decide) hn,
      List.dropLast_cons_of_ne_nil hne, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, Nat.sub_zero, Nat.ofDigits_append,
      Nat.ofDigits_singleton, List.length_append, List.length_map,
      List.length_reverse, List.length_dropLast, List.length_cons, List.length_nil,
      hlen, Nat.add_sub_cancel, pow_succ]
    ring
  · intro n hn
    have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlen := Nat.length_digits 2 n (by decide) (by omega)
    have hd : Nat.digits 2 (2 * n + 1) = 1 :: Nat.digits 2 n := by
      simpa only [Nat.add_comm] using
        Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))
    simp only [a, hd, List.dropLast_cons_of_ne_nil hne, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, Nat.sub_self,
      Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_append,
      List.length_map, List.length_reverse, List.length_dropLast,
      List.length_cons, List.length_nil, hlen, Nat.add_sub_cancel, pow_succ]
    ring
  · intro n hn
    have restore (L : List ℕ) :
        Nat.digits 2 (Nat.ofDigits 2 (L.map (fun d => 1 - d) ++ [1])) =
          L.map (fun d => 1 - d) ++ [1] := by
      apply Nat.digits_ofDigits 2 (by decide)
      · intro d hd
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hd
        rcases hd with ⟨x, _, rfl⟩ | rfl <;> omega
      · intro h
        simp
    have count_complement (L : List ℕ) :
        (L.map (fun d => 1 - d)).count 1 = L.count 0 := by
      simp only [List.count_eq_countP, List.countP_map]
      apply List.countP_congr
      intro d hd
      simp only [Function.comp_apply, beq_iff_eq]
      omega
    have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlast : (Nat.digits 2 n).getLast hne = 1 := by
      have hlt := Nat.digits_lt_base (by decide : 1 < 2) (List.getLast_mem hne)
      have hnz := Nat.getLast_digit_ne_zero 2 (by omega : n ≠ 0)
      omega
    have hsplit : (Nat.digits 2 n).dropLast ++ [1] = Nat.digits 2 n := by
      simpa only [hlast] using List.dropLast_append_getLast hne
    have hzero : (Nat.digits 2 n).dropLast.count 0 = (Nat.digits 2 n).count 0 := by
      simpa using congrArg (List.count 0) hsplit
    simp only [a, complementRest, restore, List.count_append, count_complement,
      List.count_reverse, hzero]
    simp


end D5.S1.Digit.StephanComplementReverseRecurrence
