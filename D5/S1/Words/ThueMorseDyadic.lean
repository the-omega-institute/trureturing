/- GID: D5/S1/Words/ThueMorseDyadic
   generality: G
   mirror-B: D5/B/S1/Words/ThueMorseDyadic
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Shared dyadic block and top parity identities for the actual Thue-Morse word. -/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import Mathlib.Tactic.Ring

namespace D5.S1.Words.ThueMorseDyadic

open D5.S1.Words.Complexity
open private thueMorse_two_pow_add
  from D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd

/-- Binary digit parity splits at any dyadic block boundary. -/
theorem dyadic_block (e a r : Nat) (hr : r < 2 ^ e) :
    thueMorse (a * 2 ^ e + r) = Bool.xor (thueMorse a) (thueMorse r) := by
  induction e generalizing a r with
  | zero =>
      have : r = 0 := by simpa using hr
      subst r
      simp
  | succ e ih =>
      obtain ⟨v, rfl | rfl⟩ := r.even_or_odd'
      · have hv : v < 2 ^ e := by simp only [Nat.pow_succ] at hr; omega
        rw [show a * 2 ^ (e + 1) + 2 * v = 2 * (a * 2 ^ e + v) by
          simp only [Nat.pow_succ]; ring]
        simp only [thueMorse_two_mul, ih a v hv]
      · have hv : v < 2 ^ e := by simp only [Nat.pow_succ] at hr; omega
        rw [show a * 2 ^ (e + 1) + (2 * v + 1) = 2 * (a * 2 ^ e + v) + 1 by
          simp only [Nat.pow_succ]; ring]
        simp only [thueMorse_two_mul_add_one, ih a v hv]
        cases thueMorse a <;> cases thueMorse v <;> rfl

/-- The all-one binary word has the parity of its length. -/
theorem top_parity (e : Nat) : thueMorse (2 ^ e - 1) = (e % 2 == 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
      have hp : 0 < 2 ^ e := Nat.two_pow_pos e
      rw [show 2 ^ (e + 1) - 1 = 2 ^ e + (2 ^ e - 1) by
        simp only [Nat.pow_succ]; omega]
      rw [thueMorse_two_pow_add e _ (by omega), ih]
      rcases Nat.mod_two_eq_zero_or_one e with he | he <;> simp [Nat.add_mod, he]

end D5.S1.Words.ThueMorseDyadic
