/- GID: D5/S1/Digit/Infinite/SevenCycleJointRecords
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleJointRecords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two actual entry records share literal tails and fixed future errors. -/

import D5.S1.Digit.Infinite.SevenCycleActualRecords
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleJointRecords

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open private source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private strictRecord from D5.S1.Digit.Infinite.SevenCycleActualRecords
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open private periodic_actual_records interior_owned cell_geometry
  from D5.S1.Digit.Infinite.SevenCycleActualRecords
open private budget_bounds shifted_source_tail actual_entry
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private actual_phase actual_phase_guard from D5.S1.Digit.Infinite.SevenCycleCollisionRecords
open private feeding_scalar from D5.S1.Digit.Infinite.SevenCycleCollisionFuture
open private entry_bounds from D5.S1.Digit.Infinite.SevenCycleCollisionColors

private theorem joint_actual_records (Q : ℝ → Fin 6) (hQ : instrument Q) :
    ∃ f : LegalDigits, ∃ e : Bool → ℕ → ℝ, ∃ ef er : ℕ → ℝ, ∃ epsilon : ℝ,
      stateAddress false f ∧ window f 0 = nullLabel ∧
      originalT f = originalT (source true) ∧ kappa f = feedingEntry ∧
      strictRecord Q budget (source true)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e true) epsilon ∧
      strictRecord Q budget (source false)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e false) epsilon ∧
      strictRecord Q budget f
        (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
        ef epsilon ∧
      strictRecord Q budget (source false)
        (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
        er epsilon ∧
      ef 0 = 0 ∧ er 0 = 0 ∧
      (∀ j, 0 < j → ef j = e true j ∧ er j = e false j) ∧
      e false 0 ≠ 0 ∧ (∀ b, ¬ finiteTail (source b)) ∧ ¬ finiteTail f := by
  have hguard : stateAddress false (originalT (source true)) := by
    change stateAddress false (bitShift (source true) 3)
    convert actual_phase_guard true 1 using 1 <;> norm_num [phaseGuard]
  obtain ⟨f, hf, _⟩ := closed_observation_graph_realization.2.2.2.1 false nullLabel false
    (originalT (source true)) (by simp [lawful, outgoing, nullLabel]) hguard
  have hscalar : kappa f = feedingEntry := by
    rw [(closed_observation_graph_realization.2.2.1 f).1, hf.2.1, hf.2.2]
    change branch nullLabel (kappa (bitShift (source true) (3 * (1 : Fin 7).val))) = _
    rw [actual_phase true 1]
    simpa only [↓reduceIte] using feeding_scalar
  have htail (j : ℕ) (hj : 0 < j) :
      bitShift f (3 * j) = bitShift (source true) (3 * j) := by
    apply Subtype.ext
    funext i
    have h := congrArg (fun z : LegalDigits => z.val (i + 3 * j - 3)) hf.2.2
    simpa only [originalT, bitShift, show i + 3 * j - 3 + 3 = i + 3 * j by omega] using h
  obtain ⟨e, epsilon, hu, hv⟩ := periodic_actual_records Q hQ
  let epsilon' := min epsilon budget
  have hp : 0 < epsilon' := lt_min hu.1 budget_bounds.2.2.1
  have hsmall : epsilon' ≤ epsilon := min_le_left _ _
  have hbeta : epsilon' ≤ budget := min_le_right _ _
  have weaken (x : LegalDigits) (r : ℕ → Fin 6) (ex : ℕ → ℝ)
      (hx : strictRecord Q budget x r ex epsilon) : strictRecord Q budget x r ex epsilon' := by
    refine ⟨hp, ?_⟩
    intro j
    obtain ⟨hb, hs, hc⟩ := hx.2 j
    exact ⟨by linarith, hs, hc⟩
  let ef (j : ℕ) := if j = 0 then 0 else e true j
  let er (j : ℕ) := if j = 0 then 0 else e false j
  have make_second (x : LegalDigits) (ex : ℕ → ℝ)
      (h0 : kappa x ∈ Set.Ioo (cellLower 2) (cellUpper 2))
      (hfuture : ∀ j, 0 < j →
        |ex j| ≤ budget - epsilon ∧
        kappa (bitShift x (3 * j)) + ex j ∈ stateInterval false ∧
        Q (kappa (bitShift x (3 * j)) + ex j) =
          phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) :
      strictRecord Q budget x
        (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
        (fun j => if j = 0 then 0 else ex j) epsilon' := by
    refine ⟨hp, ?_⟩
    intro j
    by_cases hj : j = 0
    · subst j
      simp only [↓reduceIte, bitShift, Nat.mul_zero, Nat.add_zero, add_zero, abs_zero]
      refine ⟨by linarith, ?_, interior_owned Q hQ 2 _ h0⟩
      have hc := cell_geometry 2
      exact ⟨hc.1.trans h0.1.le, h0.2.le.trans hc.2.2⟩
    · simp only [hj, ↓reduceIte]
      obtain ⟨hb, hs, hc⟩ := hfuture j (by omega)
      exact ⟨by linarith, hs, hc⟩
  have hfr : strictRecord Q budget f
      (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
      ef epsilon' := by
    refine make_second f (e true) ?_ ?_
    · rw [hscalar]
      exact entry_bounds.2.2.2.2.2
    · intro j hj
      rw [htail j hj]
      exact hu.2 j
  have hvr : strictRecord Q budget (source false)
      (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
      er epsilon' := by
    refine make_second (source false) (e false) ?_ ?_
    · rw [actual_entry]
      exact entry_bounds.2.2.2.2.1
    · exact fun j _ => hv.2 j
  have hn (b : Bool) : ¬ finiteTail (source b) := by
    rintro ⟨N, hN⟩
    have h := hN (21 * (N + 1) + 4) (by omega)
    norm_num [source, Nat.add_mod, Nat.mul_mod] at h
  refine ⟨f, e, ef, er, epsilon', hf.1, hf.2.1, hf.2.2, hscalar,
    weaken _ _ _ hu, weaken _ _ _ hv, hfr, hvr, rfl, rfl, ?_, ?_, hn, ?_⟩
  · intro j hj
    simp [ef, er, show j ≠ 0 by omega]
  · intro he
    have h := (hv.2 0).2.2
    have h2 : Q (kappa (source false)) = 2 := by
      apply interior_owned Q hQ 2
      rw [actual_entry]
      exact entry_bounds.2.2.2.2.1
    simp only [Nat.mul_zero, bitShift, Nat.add_zero, he, add_zero] at h
    rw [h2] at h
    norm_num [phaseColor] at h
    have hc := congrArg Fin.val h
    norm_num at hc
  · rintro ⟨N, hN⟩
    apply hn true
    refine ⟨N + 3, ?_⟩
    intro i hi
    have h := congrArg (fun z : LegalDigits => z.val (i - 3)) hf.2.2
    simp only [originalT, bitShift, Nat.sub_add_cancel (by omega : 3 ≤ i)] at h
    exact h.symm.trans (hN i (by omega))

end D5.S1.Digit.Infinite.SevenCycleJointRecords
