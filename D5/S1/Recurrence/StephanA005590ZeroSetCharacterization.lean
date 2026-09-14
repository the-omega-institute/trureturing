/- GID: D5/S1/Recurrence/StephanA005590ZeroSetCharacterization
   generality: I
   mirror-B: D5/B/S1/Recurrence/StephanA005590ZeroSetCharacterization
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Stephan's A005590 zeros are exactly the binary words without adjacent ones. -/

import Mathlib.Tactic.Linarith

namespace D5.S1.Recurrence.StephanA005590ZeroSetCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The integer sequence A005590. -/
def r : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 2 = 0 then r ((n + 2) / 2)
      else r ((n + 2) / 2 + 1) - r ((n + 2) / 2)
termination_by n => n
decreasing_by all_goals omega

@[simp] private theorem r_zero : r 0 = 0 := by
  rw [r]

@[simp] private theorem r_one : r 1 = 1 := by
  rw [r]

@[simp] private theorem r_two_mul (n : ℕ) : r (2 * n) = r n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, r]
      rw [if_pos (by omega)]
      congr 1
      omega

@[simp] private theorem r_two_mul_add_one (n : ℕ) :
    r (2 * n + 1) = r (n + 1) - r n := by
  cases n with
  | zero => rw [show 2 * 0 + 1 = 1 by omega, r_one, r_zero, sub_zero]
  | succ n =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, r]
      rw [if_neg (by omega)]
      have hdiv : (2 * n + 1 + 2) / 2 = n + 1 := by omega
      rw [hdiv]

/-- Binary representations with no two adjacent one bits. -/
def No11 (n : ℕ) : Prop := ∀ j : ℕ, (n >>> j) % 4 ≠ 3

private theorem invariant (n : ℕ) :
    (r n, r (n + 1)) ≠ (0, 0) ∧ 0 ≤ r n * (r n - r (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => norm_num [r]
      | succ n =>
          let m := (n + 1) / 2
          have hm : m < n + 1 := by dsimp [m]; omega
          rcases ih m hm with ⟨hne, hnonneg⟩
          by_cases heven : (n + 1) % 2 = 0
          · have hn : n + 1 = 2 * m := by dsimp [m]; omega
            rw [hn, r_two_mul, show 2 * m + 1 = 2 * m + 1 by rfl,
              r_two_mul_add_one]
            constructor
            · intro hzero
              apply hne
              have hfst := congrArg Prod.fst hzero
              have hsnd := congrArg Prod.snd hzero
              change r m = 0 at hfst
              change r (m + 1) - r m = 0 at hsnd
              apply Prod.ext
              · exact hfst
              · dsimp only
                omega
            · nlinarith [sq_nonneg (r m)]
          · have hn : n + 1 = 2 * m + 1 := by dsimp [m]; omega
            rw [hn, r_two_mul_add_one,
              show 2 * m + 1 + 1 = 2 * (m + 1) by omega, r_two_mul]
            constructor
            · intro hzero
              apply hne
              have hfst := congrArg Prod.fst hzero
              have hsnd := congrArg Prod.snd hzero
              change r (m + 1) - r m = 0 at hfst
              change r (m + 1) = 0 at hsnd
              apply Prod.ext
              · dsimp only
                omega
              · exact hsnd
            · nlinarith

theorem result : ∀ n : ℕ, r (3 * n) = 0 ↔ No11 n := by
  have no11_bit (b : Bool) (n : ℕ) :
      No11 (Nat.bit b n) ↔ (Nat.bit b n) % 4 ≠ 3 ∧ No11 n := by
    simp only [No11]
    constructor
    · intro h
      refine ⟨by simpa using h 0, fun j ↦ ?_⟩
      simpa only [show j + 1 = 1 + j by omega, Nat.shiftRight_add,
        Nat.bit_shiftRight_one] using h (j + 1)
    · rintro ⟨hlow, htail⟩ j
      cases j with
      | zero => simpa using hlow
      | succ j =>
          simpa only [show j + 1 = 1 + j by omega, Nat.shiftRight_add,
            Nat.bit_shiftRight_one] using htail j
  have no11_even (n : ℕ) : No11 (2 * n) ↔ No11 n := by
    rw [show 2 * n = Nat.bit false n by rfl, no11_bit]
    constructor
    · exact fun h ↦ h.2
    · intro h
      refine ⟨?_, h⟩
      simp [Nat.bit]
      omega
  have no11_one (n : ℕ) : No11 (4 * n + 1) ↔ No11 n := by
    have he : 4 * n + 1 = Nat.bit true (Nat.bit false n) := by
      simp [Nat.bit]
      omega
    rw [he, no11_bit, no11_bit]
    constructor
    · exact fun h ↦ h.2.2
    · intro h
      refine ⟨?_, ?_, h⟩
      · simp [Nat.bit]
        omega
      · simp [Nat.bit]
        omega
  have no11_three (n : ℕ) : ¬ No11 (4 * n + 3) := by
    have he : 4 * n + 3 = Nat.bit true (Nat.bit true n) := by
      simp [Nat.bit]
      omega
    intro h
    have hlow := (no11_bit true (Nat.bit true n)).1 (he ▸ h) |>.1
    apply hlow
    simp [Nat.bit]
    omega
  have zero_even (n : ℕ) : r (3 * (2 * n)) = 0 ↔ r (3 * n) = 0 := by
    rw [show 3 * (2 * n) = 2 * (3 * n) by omega, r_two_mul]
  have zero_one (n : ℕ) : r (3 * (4 * n + 1)) = 0 ↔ r (3 * n) = 0 := by
    have heq : r (3 * (4 * n + 1)) = r (3 * n) := by
      rw [show 3 * (4 * n + 1) = 2 * (6 * n + 1) + 1 by omega,
        r_two_mul_add_one,
        show 6 * n + 1 + 1 = 2 * (3 * n + 1) by omega, r_two_mul,
        show 6 * n + 1 = 2 * (3 * n) + 1 by omega, r_two_mul_add_one]
      omega
    constructor
    · intro h
      exact heq ▸ h
    · intro h
      exact heq.symm ▸ h
  have zero_three (n : ℕ) : r (3 * (4 * n + 3)) ≠ 0 := by
    intro hzero
    have hinv := invariant (3 * n + 2)
    rw [show 3 * n + 2 + 1 = 3 * n + 3 by omega] at hinv
    have heq : r (3 * (4 * n + 3)) =
        r (3 * n + 3) - 2 * r (3 * n + 2) := by
      rw [show 3 * (4 * n + 3) = 2 * (6 * n + 4) + 1 by omega,
        r_two_mul_add_one,
        show 6 * n + 4 + 1 = 2 * (3 * n + 2) + 1 by omega,
        r_two_mul_add_one,
        show 6 * n + 4 = 2 * (3 * n + 2) by omega, r_two_mul]
      rw [show 3 * n + 2 + 1 = 3 * n + 3 by omega]
      omega
    rw [heq] at hzero
    have hx : r (3 * n + 2) = 0 := by
      nlinarith [hinv.2, sq_nonneg (r (3 * n + 2))]
    have hy : r (3 * n + 3) = 0 := by omega
    apply hinv.1
    apply Prod.ext
    · exact hx
    · exact hy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [No11]
      | succ n =>
          by_cases heven : (n + 1) % 2 = 0
          · let m := (n + 1) / 2
            have hn : n + 1 = 2 * m := by dsimp [m]; omega
            rw [hn, zero_even, no11_even]
            exact ih m (by dsimp [m]; omega)
          · by_cases hhalf : (n / 2) % 2 = 0
            · let m := n / 2 / 2
              have hn : n + 1 = 4 * m + 1 := by dsimp [m]; omega
              rw [hn, zero_one, no11_one]
              exact ih m (by dsimp [m]; omega)
            · let m := n / 4
              have hn : n + 1 = 4 * m + 3 := by dsimp [m]; omega
              rw [hn]
              exact iff_of_false (zero_three m) (no11_three m)

#print axioms result

end D5.S1.Recurrence.StephanA005590ZeroSetCharacterization
