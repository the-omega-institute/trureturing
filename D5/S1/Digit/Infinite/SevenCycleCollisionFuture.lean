/- GID: D5/S1/Digit/Infinite/SevenCycleCollisionFuture
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCollisionFuture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original lawful guard phases and the null-label feeding scalar. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionRecords

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCollisionFuture

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCollisionData
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private golden_data budget_bounds entry_fixed suffix_identity source_windows
  shifted_source_tail shifted_source_windows actual_entry
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private entry_algebra entry_bounds uniform_colors
  from D5.S1.Digit.Infinite.SevenCycleCollisionColors
open private actual_phase actual_phase_mod actual_phase_guard actual_guard phase_state
  from D5.S1.Digit.Infinite.SevenCycleCollisionRecords

private theorem phase_lawful (b : Bool) (j : ℕ) :
    lawful (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (window (source b) j)
      (phaseGuard ⟨(j + 1) % 7, Nat.mod_lt _ (by decide)⟩) := by
  have h := actual_phase_guard b j
  refine ⟨?_, ?_⟩
  · simpa [stateAddress, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using h
  · simp only [outgoing, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P,
      bitShift, source, phaseGuard, Fin.val_mk]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega

private theorem feeding_scalar : branch nullLabel (phase firstEntry 1) = feedingEntry := by
  have h := entry_fixed true
  simp only [↓reduceIte] at h
  have hg := golden_data.2.1
  have hgap := entry_algebra.2.1
  simp [branch, offset, threeLabel, nullLabel] at h ⊢
  unfold feedingEntry firstEntry at *
  linarith

end D5.S1.Digit.Infinite.SevenCycleCollisionFuture
