/- GID: D5/S1/Digit/Infinite/SevenCycleActualCollision
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleActualCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint actual records yield a persistent collision in every finite horizon. -/

import D5.S1.Digit.Infinite.SevenCycleJointRecords

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleActualCollision

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open private source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private strictRecord from D5.S1.Digit.Infinite.SevenCycleActualRecords
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private joint_actual_records shared_tail_shift from D5.S1.Digit.Infinite.SevenCycleJointRecords
open private budget_bounds shifted_source_tail shifted_source_windows actual_entry entry_fixed
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private actual_phase_mod phase_state from D5.S1.Digit.Infinite.SevenCycleCollisionRecords
open private phase_lawful from D5.S1.Digit.Infinite.SevenCycleCollisionFuture

private theorem strict_member (Q : ℝ → Fin 6) (hQ : instrument Q) (x : LegalDigits)
    (r : ℕ → Fin 6) (e : ℕ → ℝ) (epsilon : ℝ)
    (hx : strictRecord Q budget x r e epsilon) (j : ℕ) :
    kappa (bitShift x (3 * j)) ∈ observation budget (r j) := by
  apply (D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width.2.2.2.2.2.2.2.2.2.1 Q hQ
    budget budget_bounds.2.2.1.le (r j))
  refine ⟨?_, kappa (bitShift x (3 * j)) + e j, (hx.2 j).2.1, (hx.2 j).2.2, ?_⟩
  · rw [← closed_observation_graph_realization.2.1 false]
    exact ⟨_, by simp [stateAddress], rfl⟩
  · have h := (hx.2 j).1
    have he : |kappa (bitShift x (3 * j)) -
        (kappa (bitShift x (3 * j)) + e j)| = |e j| := by
      rw [show kappa (bitShift x (3 * j)) -
        (kappa (bitShift x (3 * j)) + e j) = -e j by ring, abs_neg]
    rw [he]
    linarith [hx.1]

private theorem actual_collision :
    kappa (source false) ∈ observation budget 1 ∧
    kappa (source false) ∈ observation budget 2 ∧
    ∀ n : ℕ, phase firstEntry 1 ∈ entrySet budget threeLabel nullLabel 1 2 false ∩
      horizon budget (source false) 1 false n := by
  obtain ⟨Q, hQ, _, _⟩ := D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨f, e, ef, er, epsilon, hf, hl, ht, hz, hu, hv, hfr, hvr, _, _, _⟩ :=
    joint_actual_records Q hQ
  have htail (j : ℕ) (hj : 0 < j) :
      bitShift f (3 * j) = bitShift (source true) (3 * j) := by
    exact shared_tail_shift f ht j hj
  have hfirst : kappa (source true) ∈ observation budget 1 := by
    simpa [phaseColor, bitShift] using strict_member Q hQ _ _ _ _ hu 0
  have hrival1 : kappa (source false) ∈ observation budget 1 := by
    simpa [phaseColor, bitShift] using strict_member Q hQ _ _ _ _ hv 0
  have hrival2 : kappa (source false) ∈ observation budget 2 := by
    simpa [bitShift] using strict_member Q hQ _ _ _ _ hvr 0
  have hfeeding : feedingEntry ∈ observation budget 2 := by
    have h := strict_member Q hQ _ _ _ _ hfr 0
    simpa [bitShift, hz] using h
  refine ⟨hrival1, hrival2, ?_⟩
  intro n
  have all_future (n j : ℕ) (hj : 0 < j) :
      kappa (bitShift (source true) (3 * j)) ∈
        horizon budget (source false) j
          (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n := by
    induction n generalizing j with
    | zero =>
      change _ ∈ stateInterval _
      rw [actual_phase_mod]
      exact phase_state true j
    | succ n ih =>
      have hx := strict_member Q hQ _ _ _ _ hfr j
      have hy := strict_member Q hQ _ _ _ _ hvr j
      simp only [show j ≠ 0 by omega, ↓reduceIte] at hx hy
      rw [htail j hj] at hx
      refine ⟨⟨phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩, hy, hx⟩,
        window (source true) j, phaseGuard ⟨(j + 1) % 7, Nat.mod_lt _ (by decide)⟩,
        phase_lawful true j, kappa (bitShift (source true) (3 * (j + 1))),
        ih (j + 1) (by omega), ?_⟩
      have h := (closed_observation_graph_realization.2.2.1
        (bitShift (source true) (3 * j))).1
      simpa only [shifted_source_windows, Nat.add_zero, shifted_source_tail] using h
  have hs : phase firstEntry 1 ∈ stateInterval false := by
    convert phase_state true 1 using 1 <;> norm_num [phaseGuard]
  have h1 : branch threeLabel (phase firstEntry 1) ∈ observation budget 1 := by
    rw [actual_entry] at hfirst
    have he := entry_fixed true
    simp only [↓reduceIte] at he hfirst
    rwa [← he]
  have h2 : branch nullLabel (phase firstEntry 1) ∈ observation budget 2 := by
    have h := (closed_observation_graph_realization.2.2.1 f).1
    rw [hl, ht] at h
    change kappa f = branch nullLabel (kappa (bitShift (source true) (3 * 1))) at h
    rw [actual_phase_mod] at h
    norm_num at h
    rw [← h]
    simpa [bitShift, hz] using hfeeding
  refine ⟨⟨⟨hs, h1⟩, h2⟩, ?_⟩
  have h := all_future n 1 (by decide)
  rw [actual_phase_mod] at h
  convert h using 1 <;> norm_num [phaseGuard]

end D5.S1.Digit.Infinite.SevenCycleActualCollision
