/- GID: D5/S3/Factorization/CubeGapFiveNoSquare
   generality: G
   mirror-B: D5/B/S3/Factorization/CubeGapFiveNoSquare
   mirror-E: none(waiver:symbolic-arithmetic-no-numerical-evidence)
   anchors: []
   utility: none
   digest: Cubes five apart never differ by a perfect square. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The difference of two cubes five apart is a quadratic in the smaller index.
Expanded, every term but the constant carries a factor of three, and the
constant leaves two. So the difference is always two modulo three, while a
square is never two modulo three. The two residue sets are disjoint, which
settles the question without any descent or size argument.

Subtraction of naturals truncates, so the difference is stated in the
expanded form and the cube form is recovered separately, where the
subtraction is provably not truncating.
-/

namespace D5.S3.Factorization.CubeGapFiveNoSquare

/-- The difference of cubes five apart, in expanded form. -/
def gap (n : ℕ) : ℕ := 5 * (3 * n ^ 2 + 15 * n + 25)

/-- The expanded form is the difference of the two cubes. The subtraction does
not truncate because the larger cube dominates. -/
theorem gap_eq_cube_sub (n : ℕ) : gap n = (n + 5) ^ 3 - n ^ 3 := by
  have h : (n + 5) ^ 3 = n ^ 3 + gap n := by
    simp only [gap]; ring
  omega

/-- The escape content: the difference is two modulo three for every index,
whereas a square is zero or one. -/
theorem gap_mod_three (n : ℕ) : gap n % 3 = 2 := by
  simp only [gap]
  omega

/-- No square modulo three equals two. -/
theorem sq_mod_three_ne_two (m : ℕ) : m ^ 2 % 3 ≠ 2 := by
  have hsplit : m = 3 * (m / 3) + m % 3 := (Nat.div_add_mod m 3).symm
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have expand : m ^ 2
      = 3 * (3 * (m / 3) ^ 2 + 2 * (m / 3) * (m % 3)) + (m % 3) ^ 2 := by
    conv_lhs => rw [hsplit]
    ring
  rcases hr with h | h | h <;> rw [expand, h] <;> omega

/-- Klaus Purath's May 15, 2026 conjecture for OEIS A038867. -/
theorem cube_gap_five_ne_sq (n m : ℕ) : m ^ 2 ≠ gap n := by
  intro h
  have := gap_mod_three n
  rw [← h] at this
  exact sq_mod_three_ne_two m this

/-- The same statement in the source's own form. -/
theorem cube_gap_five_ne_sq_sub (n m : ℕ) : m ^ 2 ≠ (n + 5) ^ 3 - n ^ 3 := by
  rw [← gap_eq_cube_sub]
  exact cube_gap_five_ne_sq n m

#print axioms gap_mod_three
#print axioms sq_mod_three_ne_two
#print axioms cube_gap_five_ne_sq
#print axioms cube_gap_five_ne_sq_sub

end D5.S3.Factorization.CubeGapFiveNoSquare
