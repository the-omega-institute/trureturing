/- GID: D5/S1/Digit/Infinite/SevenCycleSourceFibres
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleSourceFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every shifted seven-cycle source has a unique actual address over its scalar. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionRecords

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleSourceFibres

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.SignedSeriesRange (signedValue signed_series_range v)
open private source from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres

private theorem seam_tail (w : List Block) :
    ∃ N : ℕ, ∀ n, N ≤ n → (prependWord w v).val n ≠ (prependWord w v).val (n + 1) := by
  induction w with
  | nil =>
    refine ⟨0, ?_⟩
    intro n _
    simp only [prependWord, v]
    intro h
    have h' := Bool.eq_iff_iff.mp h
    simp only [decide_eq_true_eq] at h'
    omega
  | cons c w ih =>
    obtain ⟨N, hN⟩ := ih
    cases c with
    | zero =>
      refine ⟨N + 1, ?_⟩
      intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact hN k (by omega)
    | oneZero =>
      refine ⟨N + 2, ?_⟩
      intro n hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
      subst n
      simpa [prependWord, prependBlock, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hN k (by omega)

private theorem source_not_seam (b : Bool) (j : ℕ) :
    signedValue (bitShift (source b) (3 * j)) ∉ Set.range seam := by
  have hno (w : List Block) : bitShift (source b) (3 * j) ≠ prependWord w v := by
    intro h
    obtain ⟨N, hN⟩ := seam_tail w
    have he := hN (21 * (N + 3 * j + 1) + 5 - 3 * j) (by omega)
    rw [← h] at he
    simp only [bitShift, source] at he
    have h0 : (21 * (N + 3 * j + 1) + 5 - 3 * j + 3 * j) % 21 = 5 := by omega
    have h1 : (21 * (N + 3 * j + 1) + 5 - 3 * j + 1 + 3 * j) % 21 = 6 := by omega
    simp [h0, h1] at he
  rintro ⟨w, hw⟩
  have h := ((signed_series_fibres.1 w).2 (bitShift (source b) (3 * j))).mp hw.symm
  rcases h with h | h
  · simp only [leftStream] at h
    exact hno _ h
  · simp only [rightStream] at h
    exact hno _ h

private theorem source_fibre (b : Bool) (j : ℕ) (x : LegalDigits)
    (hx : kappa x = kappa (bitShift (source b) (3 * j))) :
    x = bitShift (source b) (3 * j) := by
  have hs : signedValue x = signedValue (bitShift (source b) (3 * j)) := by
    rw [closed_observation_graph_realization.1, closed_observation_graph_realization.1] at hx
    have ht : t ≠ 0 := ne_of_gt (inv_pos.mpr Real.goldenRatio_pos)
    exact neg_injective ((div_left_inj' (pow_ne_zero 2 ht)).mp hx)
  have hm : signedValue (bitShift (source b) (3 * j)) ∈
      Set.Icc D5.S1.Digit.Infinite.SignedSeriesRange.a
        D5.S1.Digit.Infinite.SignedSeriesRange.b := by
    rw [← signed_series_range.1]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy, hu⟩ := signed_series_fibres.2.2 _ hm (source_not_seam b j)
  exact (hu x hs).trans (hu _ rfl).symm

end D5.S1.Digit.Infinite.SevenCycleSourceFibres
