/- GID: D5/S3/Factorization/GoldenCubicBlockNoncube
   generality: I
   mirror-B: D5/B/S3/Factorization/GoldenCubicBlockNoncube
   mirror-E: none(waiver:finite-residue-obstruction)
   anchors: [D5/S1/Scale/GoldenCubicBlockCongruences]
   utility: none
   digest: Every actual golden cubic block is a noncube, by its four-state orbit modulo seven. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.GoldenCubicBlockNoncube

open D5.S1.Scale
open D5.S0.Carrier

/-- The cubic Lucas block `L_(3^j)^2 + 3` is never an integer cube.
Its recurrence runs through `4, 6, 3, 1` modulo seven, giving block
residues `5, 4, 5, 4`; cubes modulo seven have residues `0, 1, 6`. -/
theorem golden_cubic_block_not_cube (j : ℕ) (hj : 1 ≤ j) :
    ¬ ∃ t : ℤ, t ^ 3 = goldenLucas (3 ^ j) ^ 2 + 3 := by
  have orbit_step (z : ZMod 7)
      (hz : z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 6) :
      z * (z ^ 2 + 3) = 1 ∨ z * (z ^ 2 + 3) = 3 ∨
        z * (z ^ 2 + 3) = 4 ∨ z * (z ^ 2 + 3) = 6 := by
    rcases hz with h | h | h | h <;> subst z <;> decide
  have orbit : ∀ k : ℕ,
      (((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 7) = 1 ∨
        ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 7) = 3 ∨
        ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 7) = 4 ∨
        ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 7) = 6) := by
    intro k
    induction k with
    | zero =>
        right; right; left
        norm_num [goldenLucas, trace, phi, pow_succ]
    | succ k ih =>
        have hstep :
            ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 7) =
              ((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 7) *
                (((goldenLucas (3 ^ (k + 1)) : ℤ) : ZMod 7) ^ 2 + 3) := by
          rw [(golden_cubic_lucas_block (k + 1) (by omega)).2.2.2.2.2]
          push_cast
          ring
        change (((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 7) = 1 ∨
          ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 7) = 3 ∨
          ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 7) = 4 ∨
          ((goldenLucas (3 ^ ((k + 1) + 1)) : ℤ) : ZMod 7) = 6)
        rw [hstep]
        exact orbit_step _ ih
  have block_residue (z : ZMod 7)
      (hz : z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 6) :
      z ^ 2 + 3 = 4 ∨ z ^ 2 + 3 = 5 := by
    rcases hz with h | h | h | h <;> subst z <;> decide
  have cube_residue (z : ZMod 7) : z ^ 3 ≠ 4 ∧ z ^ 3 ≠ 5 := by
    fin_cases z <;> decide
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm] at hk
  subst j
  intro ⟨t, ht⟩
  have hb : (((goldenLucas (3 ^ (k + 1)) ^ 2 + 3 : ℤ) : ZMod 7) = 4 ∨
      ((goldenLucas (3 ^ (k + 1)) ^ 2 + 3 : ℤ) : ZMod 7) = 5) := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using
      (block_residue _ (orbit k))
  have hcube := congrArg (fun z : ℤ => (z : ZMod 7)) ht
  simp only [Int.cast_pow] at hcube
  rcases hb with hfour | hfive
  · rw [hfour] at hcube
    exact (cube_residue (t : ZMod 7)).1 hcube
  · rw [hfive] at hcube
    exact (cube_residue (t : ZMod 7)).2 hcube

#print axioms golden_cubic_block_not_cube

end D5.S3.Factorization.GoldenCubicBlockNoncube
