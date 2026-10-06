/- GID: D5/S1/Digit/Infinite/SevenCycleCollisionFuture
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCollisionFuture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One fixed actual tail survives every finite future horizon. -/

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

private theorem actual_colors (b : Bool) (j : ℕ) :
    kappa (bitShift (source b) (3 * j)) ∈
      observation budget (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
  let r : Fin 7 := ⟨j % 7, Nat.mod_lt _ (by decide)⟩
  have hx : kappa (bitShift (source b) (3 * j)) ∈ stateInterval false := by
    rw [← closed_observation_graph_realization.2.1 false]
    exact ⟨_, by simp [stateAddress], rfl⟩
  have hi : kappa (bitShift (source b) (3 * j)) ∈
      Set.Ioo (cellLower (phaseColor r) - budget) (cellUpper (phaseColor r) + budget) := by
    rw [actual_phase_mod]
    change phase (if b then firstEntry else rivalEntry) r ∈
      Set.Ioo (cellLower (phaseColor r) - budget) (cellUpper (phaseColor r) + budget)
    by_cases hr : r = 0
    · rw [hr]
      cases b
      · simpa [phase, phaseColor] using entry_bounds.2.2.2.1
      · simpa [phase, phaseColor] using entry_bounds.2.2.1
    · apply uniform_colors _ _ r hr
      cases b
      · exact entry_bounds.2.1
      · exact entry_bounds.1
  change max (-1) (cellLower (phaseColor r) - budget) ≤ _ ∧
    _ ≤ min (1 + t) (cellUpper (phaseColor r) + budget)
  exact ⟨max_le hx.1 hi.1.le, le_min hx.2 hi.2.le⟩

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

private theorem all_horizons (n j : ℕ) :
    kappa (bitShift (source true) (3 * j)) ∈
      horizon budget (source false) j
        (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n := by
  induction n generalizing j with
  | zero =>
    change _ ∈ stateInterval _
    rw [actual_phase_mod]
    exact phase_state true j
  | succ n ih =>
    refine ⟨⟨phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩,
      actual_colors false j, actual_colors true j⟩,
      window (source true) j,
      phaseGuard ⟨(j + 1) % 7, Nat.mod_lt _ (by decide)⟩,
      phase_lawful true j,
      kappa (bitShift (source true) (3 * (j + 1))), ih (j + 1), ?_⟩
    have h := (closed_observation_graph_realization.2.2.1
      (bitShift (source true) (3 * j))).1
    simpa only [shifted_source_windows, Nat.add_zero, shifted_source_tail] using h

private theorem feeding_scalar : branch nullLabel (phase firstEntry 1) = feedingEntry := by
  have h := entry_fixed true
  simp only [↓reduceIte] at h
  have hg := golden_data.2.1
  have hgap := entry_algebra.2.1
  simp [branch, offset, threeLabel, nullLabel] at h ⊢
  unfold feedingEntry firstEntry at *
  linarith

private theorem feeding_color : feedingEntry ∈ observation budget 2 ∧
    rivalEntry ∈ observation budget 2 := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  have hb : 0 < budget := budget_bounds.2.2.1
  have hc (x : ℝ) (hx : x ∈ Set.Ioo (cellLower 2) (cellUpper 2)) :
      x ∈ observation budget 2 := by
    norm_num [cellLower, cellUpper, cuts, lambda] at hx
    have hs : x ∈ stateInterval false := by
      simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
      constructor <;> nlinarith
    change max (-1) (cellLower 2 - budget) ≤ x ∧ x ≤ min (1 + t) (cellUpper 2 + budget)
    constructor
    · apply max_le
      · exact hs.1
      · have hx' := hx.1
        norm_num [cellLower, cuts, lambda]
        linarith
    · apply le_min
      · exact hs.2
      · have hx' := hx.2
        norm_num [cellUpper, cuts, lambda]
        linarith
  exact ⟨hc _ entry_bounds.2.2.2.2.2, hc _ entry_bounds.2.2.2.2.1⟩

private theorem persistent_entry (n : ℕ) :
    phase firstEntry 1 ∈ entrySet budget threeLabel nullLabel 1 2 false ∩
      horizon budget (source false) 1 false n := by
  have hx : phase firstEntry 1 ∈ stateInterval false := by
    convert phase_state true 1 using 1 <;> norm_num [phaseGuard]
  have h1 : branch threeLabel (phase firstEntry 1) ∈ observation budget 1 := by
    have h := actual_colors true 0
    change kappa (source true) ∈ observation budget 1 at h
    rw [actual_entry] at h
    have hf := entry_fixed true
    simp only [↓reduceIte] at hf h
    rwa [← hf]
  have h2 : branch nullLabel (phase firstEntry 1) ∈ observation budget 2 := by
    rw [feeding_scalar]
    exact feeding_color.1
  refine ⟨⟨⟨hx, h1⟩, h2⟩, ?_⟩
  have h := all_horizons n 1
  rw [actual_phase_mod] at h
  convert h using 1 <;> norm_num [phaseGuard]

end D5.S1.Digit.Infinite.SevenCycleCollisionFuture
