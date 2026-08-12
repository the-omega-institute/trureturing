/- GID: D5/S1/Deficit/GoldenFiberFirstIndex
   generality: I
   mirror-B: D5/B/S1/Deficit/GoldenFiberFirstIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equate the two exact floor formulas for the first golden fiber index. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Ring

namespace D5.S1.Deficit.GoldenFiberFirstIndex

/-- The corrected and compressed formulas for the first index of a positive
golden fiber agree. -/
theorem golden_fiber_first_index_forms_eq (a : ℕ) (ha : 1 ≤ a) :
    ⌊(a : ℝ) * Real.goldenRatio - Real.goldenRatio ^ 2⌋ + 1 =
      ⌊((a - 1 : ℕ) : ℝ) * Real.goldenRatio⌋ := by
  have hargument :
      (a : ℝ) * Real.goldenRatio - Real.goldenRatio ^ 2 =
        ((a - 1 : ℕ) : ℝ) * Real.goldenRatio - 1 := by
    rw [Real.goldenRatio_sq, Nat.cast_sub ha]
    norm_num
    ring
  rw [hargument, Int.floor_sub_one]
  omega

example : ℕ := 1

example : 1 ≤ (1 : ℕ) := by omega

end D5.S1.Deficit.GoldenFiberFirstIndex
