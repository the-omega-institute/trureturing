/- GID: D5/S3/Factorization/GoldenCubicBlockNonFifthPower
   generality: I
   mirror-B: D5/B/S3/Factorization/GoldenCubicBlockNonFifthPower
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual Lucas cubic blocks avoid fifth powers by induction modulo eleven. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.GoldenCubicBlockNonFifthPower

open D5.S1.Scale
open D5.S0.Carrier

/-- No actual positive-index Lucas cubic block is an integer fifth power.
The actual Lucas recurrence has orbit `4, 10, 7, 1` modulo eleven,
so its block has residue `8` or `4`, whereas fifth powers have
residue `0`, `1`, or `10`. -/
theorem golden_cubic_block_not_fifth_power (j : ℕ) (hj : 1 ≤ j) :
    ¬ ∃ t : ℤ, t ^ 5 = goldenLucas (3 ^ j) ^ 2 + 3 := by
  have orbit_step (z : ZMod 11)
      (hz : z = 1 ∨ z = 4 ∨ z = 10 ∨ z = 7) :
      z * (z ^ 2 + 3) = 1 ∨ z * (z ^ 2 + 3) = 4 ∨
        z * (z ^ 2 + 3) = 10 ∨ z * (z ^ 2 + 3) = 7 := by
    rcases hz with h | h | h | h <;> subst z <;> decide
  have orbit : ∀ k : ℕ,
      (((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 11) = 1 ∨
        ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 11) = 4 ∨
        ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 11) = 10 ∨
        ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 11) = 7) := by
    intro k
    induction k with
    | zero =>
        right; left
        norm_num [goldenLucas, trace, phi, pow_succ]
    | succ k ih =>
        have hstep :
            ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 11) =
              ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 11) *
                (((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 11) ^ 2 + 3) := by
          rw [(golden_cubic_lucas_block (k + 1) (by omega)).2.2.2.2.2]
          push_cast
          ring
        change (((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 11) = 1 ∨
          ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 11) = 4 ∨
          ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 11) = 10 ∨
          ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 11) = 7)
        rw [hstep]
        exact orbit_step _ ih
  have block_residue (z : ZMod 11)
      (hz : z = 1 ∨ z = 4 ∨ z = 10 ∨ z = 7) :
      z ^ 2 + 3 = 4 ∨ z ^ 2 + 3 = 8 := by
    rcases hz with h | h | h | h <;> subst z <;> decide
  have fifth_residue (z : ZMod 11) : z ^ 5 ≠ 4 ∧ z ^ 5 ≠ 8 := by
    fin_cases z <;> decide
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm] at hk
  subst j
  intro ⟨t, ht⟩
  have hb : (((goldenLucas (3 ^ (k + 1)) ^ 2 + 3 : ℤ) : ZMod 11) = 4 ∨
      ((goldenLucas (3 ^ (k + 1)) ^ 2 + 3 : ℤ) : ZMod 11) = 8) := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using
      (block_residue _ (orbit k))
  have hfifth := congrArg (fun z : ℤ => (z : ZMod 11)) ht
  simp only [Int.cast_pow] at hfifth
  rcases hb with hfour | height
  · rw [hfour] at hfifth
    exact (fifth_residue (t : ZMod 11)).1 hfifth
  · rw [height] at hfifth
    exact (fifth_residue (t : ZMod 11)).2 hfifth

#print axioms golden_cubic_block_not_fifth_power

end D5.S3.Factorization.GoldenCubicBlockNonFifthPower
