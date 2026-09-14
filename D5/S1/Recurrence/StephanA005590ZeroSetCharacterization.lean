/- GID: D5/S1/Recurrence/StephanA005590ZeroSetCharacterization
   generality: I
   mirror-B: D5/B/S1/Recurrence/StephanA005590ZeroSetCharacterization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise, mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Stephan's A005590 zeros are exactly the binary words without adjacent ones. -/

import Mathlib.Data.Nat.Bitwise
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
def No11 (n : ℕ) : Prop := n &&& (n >>> 1) = 0

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

end D5.S1.Recurrence.StephanA005590ZeroSetCharacterization
