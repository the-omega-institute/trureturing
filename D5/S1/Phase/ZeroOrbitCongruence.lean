/- GID: D5/S1/Phase/ZeroOrbitCongruence
   generality: I
   mirror-B: D5/B/S1/Phase/ZeroOrbitCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Isolate the finite and global congruence steps in the zero-orbit 36 theorem. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace D5.S1.Phase.ZeroOrbitCongruence

/-- An Eisenstein norm has residue zero or one modulo three. -/
theorem eisenstein_norm_mod_three (x y : ZMod 3) :
    x ^ 2 - x * y + y ^ 2 = 0 ∨ x ^ 2 - x * y + y ^ 2 = 1 := by
  fin_cases x <;> fin_cases y <;> decide

/-- The local candidates modulo 36 reduce to zero when the represented number
is globally constrained to be an Eisenstein norm modulo three. -/
theorem thirty_six_dvd_of_local_candidates_and_eisenstein_norm
    (m : ℕ) (x y : ZMod 3)
    (hLocal : m % 36 = 0 ∨ m % 36 = 8)
    (hNorm : (m : ZMod 3) = x ^ 2 - x * y + y ^ 2) :
    36 ∣ m := by
  rcases hLocal with hZero | hEight
  · exact Nat.dvd_of_mod_eq_zero hZero
  · exfalso
    have hDecomposition : 8 + 36 * (m / 36) = m := by
      calc
        8 + 36 * (m / 36) = m % 36 + 36 * (m / 36) := by rw [hEight]
        _ = m := Nat.mod_add_div m 36
    have hmTwo : (m : ZMod 3) = 2 := by
      have hCast := congrArg (fun n : ℕ => (n : ZMod 3)) hDecomposition
      have hEight : (8 : ZMod 3) = 2 := by decide
      have hThirtySix : (36 : ZMod 3) = 0 := by decide
      norm_num at hCast
      rw [hEight, hThirtySix, zero_mul, add_zero] at hCast
      exact hCast.symm
    have hResidue := eisenstein_norm_mod_three x y
    rw [← hNorm, hmTwo] at hResidue
    have hTwoNeZero : (2 : ZMod 3) ≠ 0 := by decide
    have hTwoNeOne : (2 : ZMod 3) ≠ 1 := by decide
    rcases hResidue with h | h
    · exact hTwoNeZero h
    · exact hTwoNeOne h

end D5.S1.Phase.ZeroOrbitCongruence
