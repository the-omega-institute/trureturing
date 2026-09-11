/- GID: D5/S1/Digit/PrimeDigitBaseClassification
   generality: G
   mirror-B: D5/B/S1/Digit/PrimeDigitBaseClassification
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs]
   utility: none
   digest: Prime-digit bases exist exactly outside zero, one, four, six, and nine. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.PrimeDigitBaseClassification

/-- Zero is excluded explicitly because `Nat.digits b 0` is the empty list. -/
def HasPrimeDigitBase (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∃ b : ℕ, 1 < b ∧ ∀ d ∈ Nat.digits b n, Nat.Prime d

/-- The two uniform certificates, with digits in little-endian order. -/
theorem prime_digit_base_certificate (n : ℕ) (hn : 10 ≤ n) :
    (1 < (n - 2) / 2 ∧ Nat.digits ((n - 2) / 2) n = [2, 2]) ∨
      (1 < (n - 3) / 2 ∧ Nat.digits ((n - 3) / 2) n = [3, 2]) := by
  by_cases heven : n % 2 = 0
  · have hb : 2 < (n - 2) / 2 := by omega
    have hnrep : n = 2 + (n - 2) / 2 * 2 := by omega
    refine Or.inl ⟨by omega, ?_⟩
    conv_lhs => arg 2; rw [hnrep]
    rw [Nat.digits_add _ (by omega) 2 2 hb (Or.inl (by decide)),
      Nat.digits_of_lt _ 2 (by decide) hb]
  · have hb : 3 < (n - 3) / 2 := by omega
    have hnrep : n = 3 + (n - 3) / 2 * 2 := by omega
    refine Or.inr ⟨by omega, ?_⟩
    conv_lhs => arg 2; rw [hnrep]
    rw [Nat.digits_add _ (by omega) 3 2 hb (Or.inl (by decide)),
      Nat.digits_of_lt _ 2 (by decide) (by omega)]

/-- The zero-set conjecture for OEIS A390088 (Felix Huber, 2025-10-29). -/
theorem a390088 (n : ℕ) :
    HasPrimeDigitBase n ↔ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 4 ∧ n ≠ 6 ∧ n ≠ 9 := by
  constructor
  · rintro ⟨hn, b, hb, hprime⟩
    have excluded (m : ℕ) (hm : m = 1 ∨ m = 4 ∨ m = 6 ∨ m = 9) : n ≠ m := by
      intro hnm
      subst n
      by_cases hmb : m < b
      · have hp : Nat.Prime m :=
          hprime m (by rw [Nat.digits_of_lt b m hn hmb]; simp)
        rcases hm with rfl | rfl | rfl | rfl <;> revert hp <;> decide
      · have hm10 : m < 10 := by omega
        have finite_exclusions : ∀ m b : Fin 10,
            (m.val = 1 ∨ m.val = 4 ∨ m.val = 6 ∨ m.val = 9) → 1 < b.val →
              ¬ (∀ d ∈ Nat.digits b.val m.val, Nat.Prime d) := by decide
        exact finite_exclusions ⟨m, hm10⟩ ⟨b, by omega⟩ hm hb hprime
    exact ⟨hn, excluded 1 (by omega), excluded 4 (by omega),
      excluded 6 (by omega), excluded 9 (by omega)⟩
  · rintro ⟨hn, h1, h4, h6, h9⟩
    refine ⟨hn, ?_⟩
    by_cases hlarge : 10 ≤ n
    · obtain ⟨hb, hd⟩ | ⟨hb, hd⟩ := prime_digit_base_certificate n hlarge
      · refine ⟨(n - 2) / 2, hb, ?_⟩
        simp [hd, Nat.prime_two]
      · refine ⟨(n - 3) / 2, hb, ?_⟩
        simp [hd, Nat.prime_two, Nat.prime_three]
    · have cases_small : n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 8 := by omega
      rcases cases_small with rfl | rfl | rfl | rfl | rfl
      · exact ⟨3, by decide, by decide⟩
      · exact ⟨4, by decide, by decide⟩
      · exact ⟨6, by decide, by decide⟩
      · exact ⟨8, by decide, by decide⟩
      · exact ⟨3, by decide, by decide⟩

#print axioms prime_digit_base_certificate
#print axioms a390088

end D5.S1.Digit.PrimeDigitBaseClassification
