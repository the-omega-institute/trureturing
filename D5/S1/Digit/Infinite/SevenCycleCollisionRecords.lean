/- GID: D5/S1/Digit/Infinite/SevenCycleCollisionRecords
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCollisionRecords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual periodic scalar phases and common finite-future tests. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionColors
import D5.S1.Digit.Infinite.SevenCycleSeparationRefutation

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCollisionRecords

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open private source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private source_period source_windows shifted_source_windows shifted_source_tail
  actual_entry golden_data budget_bounds entry_fixed suffix_identity
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private entry_bounds uniform_colors from D5.S1.Digit.Infinite.SevenCycleCollisionColors

private theorem actual_phase (b : Bool) (j : Fin 7) :
    kappa (bitShift (source b) (3 * j.val)) =
      phase (if b then firstEntry else rivalEntry) j := by
  let v (j : ℕ) := kappa (bitShift (source b) (3 * j))
  have hrec (j : ℕ) : v j = branch (window (source b) j) (v (j + 1)) := by
    have h := closed_observation_graph_realization.2.2.1
      (bitShift (source b) (3 * j))
    simpa only [v, shifted_source_windows, Nat.add_zero, shifted_source_tail] using h.1
  have h0 : v 0 = if b then firstEntry else rivalEntry := actual_entry b
  have h7 : v 7 = if b then firstEntry else rivalEntry := by
    change kappa (bitShift (source b) 21) = _
    rw [source_period]
    exact actual_entry b
  change v j.val = _
  fin_cases j <;>
    simp only [h0, h7, hrec 1, hrec 2, hrec 3, hrec 4, hrec 5, hrec 6] <;>
    simp [source_windows, phase, firstLabel, rivalLabel]

private theorem actual_phase_mod (b : Bool) (j : ℕ) :
    kappa (bitShift (source b) (3 * j)) =
      phase (if b then firstEntry else rivalEntry) ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by
  have hs : bitShift (source b) (3 * j) = bitShift (source b) (3 * (j % 7)) := by
    apply Subtype.ext
    funext i
    have hm : (i + 3 * j) % 21 = (i + 3 * (j % 7)) % 21 := by omega
    simp only [bitShift, source, hm]
  rw [hs]
  simpa only [Fin.val_mk] using
    actual_phase b (⟨j % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7)

private theorem actual_phase_guard (b : Bool) (j : ℕ) :
    stateAddress (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
      (bitShift (source b) (3 * j)) := by
  unfold stateAddress
  simp only [phaseGuard, decide_eq_true_eq]
  intro h
  simp only [bitShift, source, decide_eq_false_iff_not]
  omega

private theorem actual_guard (b : Bool) (j : ℕ) :
    actualGuard false (source b) j = phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by
  by_cases hj : j = 0
  · subst j; rfl
  · simp only [actualGuard, hj, ↓reduceIte, source, phaseGuard, Fin.val_mk]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega

private theorem phase_state (b : Bool) (j : ℕ) :
    phase (if b then firstEntry else rivalEntry) ⟨j % 7, Nat.mod_lt _ (by decide)⟩ ∈
      stateInterval (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
  rw [← actual_phase_mod]
  rw [← closed_observation_graph_realization.2.1 _]
  exact ⟨_, actual_phase_guard b j, rfl⟩

private theorem periodic_rival : primitiveWindowPeriod (source false) 7 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro n
    simp [source_windows, Nat.add_mod]
  · intro k hk hp
    have h := hp 0
    rw [Nat.zero_add, source_windows, source_windows] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mod, rivalLabel] at h
    have hr : k % 7 < 7 := Nat.mod_lt _ (by decide)
    rcases (show k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
      k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 by omega) with he | he | he | he | he | he | he
    · omega
    all_goals norm_num [he, firstLabel] at h
    all_goals first
      | have hc := congrArg (fun l : Label => l.val 0) h
        norm_num [threeLabel, nullLabel, fiveLabel, twoLabel] at hc <;> contradiction
      | have hc := congrArg (fun l : Label => l.val 1) h
        norm_num [threeLabel, nullLabel, fiveLabel, twoLabel] at hc <;> contradiction
      | have hc := congrArg (fun l : Label => l.val 2) h
        norm_num [threeLabel, nullLabel, fiveLabel, twoLabel] at hc <;> contradiction

end D5.S1.Digit.Infinite.SevenCycleCollisionRecords
