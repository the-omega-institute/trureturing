/- GID: D5/S1/Recurrence/FloorCounts/RotationEventCount
   generality: G
   mirror-B: D5/B/S1/Recurrence/FloorCounts/RotationEventCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Floor-difference event counts telescope with error below one. -/

import Mathlib

namespace D5.S1.Recurrence.FloorCounts.RotationEventCount

/-- The integer event weight between two successive floor samples. -/
noncomputable def eventWeight (theta alpha : ℝ) (n : ℕ) : ℤ :=
  ⌊theta + (n : ℝ) * alpha + alpha⌋ - ⌊theta + (n : ℝ) * alpha⌋

private theorem eventWeight_sum (theta alpha : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, eventWeight theta alpha n =
      ⌊theta + (N : ℝ) * alpha⌋ - ⌊theta⌋ := by
  induction N with
  | zero => simp [eventWeight]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hcast : theta + ((N + 1 : ℕ) : ℝ) * alpha =
          theta + (N : ℝ) * alpha + alpha := by
        push_cast
        ring
      rw [hcast]
      simp only [eventWeight]
      ring

/-- Rotation event counts telescope, and their discrepancy from the expected count is below one. -/
theorem bounded_event_count (theta alpha : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, eventWeight theta alpha n =
        ⌊theta + (N : ℝ) * alpha⌋ - ⌊theta⌋) ∧
      |(((∑ n ∈ Finset.range N, eventWeight theta alpha n : ℤ) : ℝ) -
          (N : ℝ) * alpha)| < 1 := by
  constructor
  · exact eventWeight_sum theta alpha N
  · rw [eventWeight_sum]
    let x : ℝ := theta + (N : ℝ) * alpha
    have htheta : (⌊theta⌋ : ℝ) + Int.fract theta = theta := Int.floor_add_fract theta
    have hx : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
    have hdiff : (((⌊x⌋ - ⌊theta⌋ : ℤ) : ℝ) - (N : ℝ) * alpha) =
        Int.fract theta - Int.fract x := by
      dsimp [x] at hx ⊢
      push_cast
      linarith
    rw [show theta + (N : ℝ) * alpha = x by rfl, hdiff]
    rw [abs_lt]
    constructor <;> linarith [Int.fract_nonneg theta, Int.fract_lt_one theta,
      Int.fract_nonneg x, Int.fract_lt_one x]

#print axioms bounded_event_count

end D5.S1.Recurrence.FloorCounts.RotationEventCount
