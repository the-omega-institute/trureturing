/- GID: D5/S3/Quantum/Fibers/FiveModeProbabilityReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/FiveModeProbabilityReconstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Classical five-event probability reconstruction from three marginals and one overlap parameter. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Classical five-event probability reconstruction from three marginals and one overlap
parameter. This module supplies a probability-coordinate bridge only; it does not assert a
Born rule, a phase interpretation, or a native AURIC/FIB quantum realization. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Fibers.FiveModeProbabilityReconstruction

/-- The admissible lower endpoint for the overlap parameter. -/
def lowerBound (X Y Z : ℝ) : ℝ := max 0 (X + Y + Z - 1)

/-- The admissible upper endpoint for the overlap parameter. -/
def upperBound (X Y : ℝ) : ℝ := min X Y

/-- The five classical event masses determined by three marginals and an overlap. -/
def probabilities (X Y Z κ : ℝ) : Fin 5 → ℝ :=
  ![1 - X - Y - Z + κ, X - κ, Z, Y - κ, κ]

/-- The reconstructed masses always have total mass one. -/
theorem probabilities_sum (X Y Z κ : ℝ) :
    ∑ i, probabilities X Y Z κ i = 1 := by
  simp [probabilities, Fin.sum_univ_succ]
  ring

/-- The endpoint inequalities make every reconstructed mass nonnegative. -/
theorem probabilities_nonneg (X Y Z κ : ℝ)
    (hZ : 0 ≤ Z)
    (hκ : lowerBound X Y Z ≤ κ ∧ κ ≤ upperBound X Y) :
    ∀ i, 0 ≤ probabilities X Y Z κ i := by
  intro i
  fin_cases i
  · have hsum : X + Y + Z - 1 ≤ κ :=
      le_trans (le_max_right 0 (X + Y + Z - 1)) hκ.1
    simp [probabilities]
    linarith
  · have hX : κ ≤ X := le_trans hκ.2 (min_le_left X Y)
    simp [probabilities]
    linarith
  · simpa [probabilities] using hZ
  · have hY : κ ≤ Y := le_trans hκ.2 (min_le_right X Y)
    simp [probabilities]
    linarith
  · simpa [probabilities] using
      (le_trans (le_max_left 0 (X + Y + Z - 1)) hκ.1)

/-- Strict endpoint inequalities and a positive middle mass make every mass positive. -/
theorem probabilities_pos (X Y Z κ : ℝ)
    (hZ : 0 < Z)
    (hκ : lowerBound X Y Z < κ ∧ κ < upperBound X Y) :
    ∀ i, 0 < probabilities X Y Z κ i := by
  intro i
  fin_cases i
  · have hsum : X + Y + Z - 1 < κ :=
      lt_of_le_of_lt (le_max_right 0 (X + Y + Z - 1)) hκ.1
    simp [probabilities]
    linarith
  · have hX : κ < X := lt_of_lt_of_le hκ.2 (min_le_left X Y)
    simp [probabilities]
    linarith
  · simpa [probabilities] using hZ
  · have hY : κ < Y := lt_of_lt_of_le hκ.2 (min_le_right X Y)
    simp [probabilities]
    linarith
  · simpa [probabilities] using
      (lt_of_le_of_lt (le_max_left 0 (X + Y + Z - 1)) hκ.1)

/-- The three marginal coordinates and overlap are recovered from the five masses. -/
theorem probabilities_recover (X Y Z κ : ℝ) :
    probabilities X Y Z κ 1 + probabilities X Y Z κ 4 = X ∧
    probabilities X Y Z κ 3 + probabilities X Y Z κ 4 = Y ∧
    probabilities X Y Z κ 2 = Z ∧
    probabilities X Y Z κ 4 = κ := by
  simp [probabilities]

end D5.S3.Quantum.Fibers.FiveModeProbabilityReconstruction
