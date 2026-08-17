/- GID: D5/S3/PrimeForms/PellFamilies/CrossingPellFamily
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PellFamilies/CrossingPellFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A crossing family is an explicit Pell sequence of discriminant 48. -/

import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.PrimeForms.PellFamilies.CrossingPellFamily

mutual
  /-- The `A` coordinate of the crossing family, beginning `3, 48, 675, ...`. -/
  def crossingA : ℕ → ℤ
    | 0 => 3
    | n + 1 => 7 * crossingA n + 24 * crossingJ n + 3

  /-- The Pell coordinate of the crossing family, beginning `1, 14, 195, ...`. -/
  def crossingJ : ℕ → ℤ
    | 0 => 1
    | n + 1 => 2 * crossingA n + 7 * crossingJ n + 1
end

private theorem one_lt_seven : 1 < (7 : ℕ) := by norm_num

private theorem crossing_coordinates_eq_pell (n : ℕ) :
    2 * crossingA n + 1 = Pell.xz one_lt_seven (n + 1) ∧
      crossingJ n = Pell.yz one_lt_seven (n + 1) := by
  induction n with
  | zero => norm_num [crossingA, crossingJ, Pell.xz, Pell.yz, Pell.pell]
  | succ n ih =>
      constructor
      · rw [crossingA, Pell.xz_succ, Pell.dz_val, ← ih.1, ← ih.2]
        norm_num [Pell.az]
        ring
      · rw [crossingJ, Pell.yz_succ, ← ih.1, ← ih.2]
        norm_num [Pell.az]
        ring

/-- Every member of the crossing recurrence lies on the Pell conic
`(2A + 1)^2 - 48j^2 = 1`. -/
theorem crossing_pell_invariant (n : ℕ) :
    (2 * crossingA n + 1) ^ 2 - 48 * crossingJ n ^ 2 = 1 := by
  rcases crossing_coordinates_eq_pell n with ⟨hA, hJ⟩
  rw [hA, hJ]
  have hpell := Pell.pell_eqz one_lt_seven (n + 1)
  rw [Pell.dz_val] at hpell
  norm_num [Pell.az] at hpell
  simpa [pow_two, Pell.az, mul_assoc] using hpell

end D5.S3.PrimeForms.PellFamilies.CrossingPellFamily
