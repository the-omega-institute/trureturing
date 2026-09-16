/- GID: D5/S1/Digit/YanevBinaryReversalPositionIdentity
   generality: G
   mirror-B: D5/B/S1/Digit/YanevBinaryReversalPositionIdentity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Yanev's binary-reversal position identity holds for every positive natural number. -/

import Mathlib.Data.Nat.Log

/-! The three definitions are total functions on natural numbers. The logarithm
is Mathlib's totalized `Nat.log`; each use as a binary logarithm in `result` has
a positive argument. Subtraction in `stripTop` is natural subtraction.

The declarations are symbolic definitions and an unbounded universal identity,
not bounded enumeration, a checker, numeric reduction, or a certified instance;
hence `utility: none`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.YanevBinaryReversalPositionIdentity

/-- OEIS A264596, using Heinz's binary recurrence. -/
def w : ℕ → ℕ :=
  Nat.binaryRec 0 (fun bit n previous => if bit then previous + n + 1 else previous)

/-- OEIS A053645, with the totalized value `stripTop 0 = 0`. -/
def stripTop (n : ℕ) : ℕ := n - 2 ^ Nat.log 2 n

/-- OEIS A030101, using Stephan's recurrence and the zero boundary from its data. -/
def rev : ℕ → ℕ :=
  Nat.binaryRec 0 fun bit n previous =>
    if bit then if n = 0 then 1 else previous + 2 ^ (Nat.log 2 n + 1) else previous

/-- Yanev's A030101/A264596 identity, stated without truncated subtraction. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    rev n + 2 * w (stripTop n) + 1 = 2 * w n := by
  induction n using Nat.binaryRec with
  | zero => omega
  | bit bit m ih =>
      have hw : w (Nat.bit bit m) = if bit then w m + m + 1 else w m := by
        simpa [w] using
          (Nat.binaryRec_eq (motive := fun _ => ℕ)
            (zero := 0)
            (bit := fun bit n previous =>
              if bit then previous + n + 1 else previous)
            bit m (Or.inl rfl))
      have hr : rev (Nat.bit bit m) =
          if bit then if m = 0 then 1 else rev m + 2 ^ (Nat.log 2 m + 1) else rev m := by
        simpa [rev] using
          (Nat.binaryRec_eq (motive := fun _ => ℕ)
            (zero := 0)
            (bit := fun bit n previous =>
              if bit then if n = 0 then 1
              else previous + 2 ^ (Nat.log 2 n + 1) else previous)
            bit m (Or.inl rfl))
      by_cases hm : m = 0
      · subst m
        cases bit <;> simp_all [Nat.bit, stripTop, w]
      · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hi := ih hmpos
        have hpow : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm
        cases bit
        · have hlog : Nat.log 2 (Nat.bit false m) = Nat.log 2 m + 1 :=
            Nat.log_two_bit hm
          have hstrip : stripTop (Nat.bit false m) = 2 * stripTop m := by
            simp only [stripTop]
            rw [hlog, Nat.pow_succ, Nat.bit_false_apply]
            omega
          simp only [Bool.false_eq_true, if_false] at hw hr
          rw [hr, hw, hstrip]
          have hwstrip : w (2 * stripTop m) = w (stripTop m) := by
            have heq : 2 * stripTop m = Nat.bit false (stripTop m) := by
              simp [Nat.bit]
            rw [heq]
            simpa [w] using
              (Nat.binaryRec_eq (motive := fun _ => ℕ)
                (zero := 0)
                (bit := fun bit n previous =>
                  if bit then previous + n + 1 else previous)
                false (stripTop m) (Or.inl rfl))
          rw [hwstrip]
          exact hi
        · have hlog : Nat.log 2 (Nat.bit true m) = Nat.log 2 m + 1 :=
            Nat.log_two_bit hm
          have hstrip : stripTop (Nat.bit true m) = 2 * stripTop m + 1 := by
            simp only [stripTop]
            rw [hlog, Nat.pow_succ, Nat.bit_true_apply]
            omega
          simp only [if_true, hm, if_false] at hw hr
          rw [hr, hw, hstrip]
          have hwstrip : w (2 * stripTop m + 1) =
              w (stripTop m) + stripTop m + 1 := by
            have heq : 2 * stripTop m + 1 = Nat.bit true (stripTop m) := by
              simp [Nat.bit]
            rw [heq]
            simpa [w] using
              (Nat.binaryRec_eq (motive := fun _ => ℕ)
                (zero := 0)
                (bit := fun bit n previous =>
                  if bit then previous + n + 1 else previous)
                true (stripTop m) (Or.inl rfl))
          rw [hwstrip]
          simp only [stripTop] at hi ⊢
          rw [Nat.pow_succ]
          have hsplit : m - 2 ^ Nat.log 2 m + 2 ^ Nat.log 2 m = m :=
            Nat.sub_add_cancel hpow
          omega

end D5.S1.Digit.YanevBinaryReversalPositionIdentity
