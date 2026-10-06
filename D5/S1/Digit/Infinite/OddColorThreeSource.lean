/- GID: D5/S1/Digit/Infinite/OddColorThreeSource
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/OddColorThreeSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd closed color words support at most two actual periodic addresses. -/

import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth
import Mathlib.Dynamics.PeriodicPts.Defs

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.OddColorThreeSource

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SignedSeriesRange (signedValue signed_series_range v)
open D5.S1.Digit.Infinite.SignedSeriesFibres
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres

private theorem shift_add (x : LegalDigits) (a b : ℕ) :
    bitShift (bitShift x a) b = bitShift x (a + b) := by
  apply Subtype.ext
  funext j
  simp only [bitShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem periodic_shift (x : LegalDigits) (d n : ℕ)
    (hx : Function.Periodic x.val d) :
    Function.Periodic (bitShift x n).val d := by
  intro j
  exact (by simpa only [bitShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx (j + n))

private theorem prepend_not_odd_periodic (w : List Block) (d : ℕ) (hd : Odd d) :
    ¬ Function.Periodic (prependWord w v).val d := by
  induction w with
  | nil =>
    intro h
    have h0 := h 0
    have hm : d % 2 = 1 := Nat.odd_iff.mp hd
    simp [prependWord, v, hm] at h0
  | cons c w ih =>
    intro h
    apply ih
    intro j
    cases c with
    | zero =>
      simpa [prependWord, prependBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h (j + 1)
    | oneZero =>
      simpa [prependWord, prependBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h (j + 2)

private theorem odd_periodic_scalar_injective (d : ℕ) (hd : Odd d)
    (x y : LegalDigits) (hx : Function.Periodic x.val d)
    (hy : Function.Periodic y.val d) (he : kappa x = kappa y) : x = y := by
  have hg := D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization.1
  have hs : signedValue x = signedValue y := by
    have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
    rw [hg x, hg y] at he
    exact neg_injective ((div_left_inj' (ne_of_gt (sq_pos_of_pos ht))).mp he)
  have hn : signedValue x ∉ Set.range seam := by
    rintro ⟨w, hw⟩
    rcases ((signed_series_fibres.1 w).2 x).mp hw.symm with h | h
    · subst x
      exact prepend_not_odd_periodic (w ++ [.zero]) d hd hx
    · subst x
      exact prepend_not_odd_periodic (w ++ [.oneZero]) d hd hx
  have hb : signedValue x ∈ Set.Icc
      D5.S1.Digit.Infinite.SignedSeriesRange.a D5.S1.Digit.Infinite.SignedSeriesRange.b := by
    rw [← signed_series_range.1]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz, hu⟩ := signed_series_fibres.2.2 _ hb hn
  exact (hu x rfl).trans (hu y hs.symm).symm

end D5.S1.Digit.Infinite.OddColorThreeSource
