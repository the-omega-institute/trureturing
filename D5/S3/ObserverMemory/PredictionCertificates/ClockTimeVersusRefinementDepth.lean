/- GID: D5/S3/ObserverMemory/PredictionCertificates/ClockTimeVersusRefinementDepth
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/ClockTimeVersusRefinementDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A one-state system has zero completion depth at every clock time, while a four-state one-step cycle has completion depth at least two; arbitrary depths are not covered. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'clock_time_does_not_determine_refinement_depth' D5 \
     Golden/Frozen/accepted` returned no matches.
   * Searches for `clock time`, `refinementDepth`, `completionDepth`,
     `distinguishingTime`, and `futureReadoutWord` found itinerary completion,
     permanent-stability, and root-pulse results, but no theorem combining clock
     time with two concrete completion-depth separation witnesses.
   * `ItineraryCompletion.completionDepth` is reused as predictive refinement
     depth. Its distinguishing-time specification is private, so the delayed
     witness unfolds the public definition and uses `Classical.choose_spec`.
   * The remaining proof uses finite enumeration, function iteration, and
     elementary natural-number arithmetic; no stronger Mathlib result applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionCertificates.ClockTimeVersusRefinementDepth

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/-- The one-state system can execute arbitrarily many clock steps. -/
def longRunUpdate : Unit -> Unit := id

/-- The one-state system exposes its unique state immediately. -/
def longRunReadout : Unit -> Unit := id

set_option backward.isDefEq.respectTransparency false in
/-- Four clock states whose readout stays flat until the final state. -/
inductive DelayedState where
  | zero
  | one
  | two
  | reveal
  deriving DecidableEq, Fintype

/-- Advance the delayed system by one clock step around its four-state cycle. -/
def delayedUpdate : DelayedState -> DelayedState
  | .zero => .one
  | .one => .two
  | .two => .reveal
  | .reveal => .zero

/-- Only the reveal state is observably different. -/
def delayedReadout : DelayedState -> Bool
  | .zero => false
  | .one => false
  | .two => false
  | .reveal => true

/-- Clock duration and predictive completion depth do not determine one another:
the one-state witness runs for every clock duration with depth zero, while one
step of the four-state witness starts a system whose completion depth is at
least two. -/
theorem clock_time_does_not_determine_refinement_depth :
    (exists (tau : Unit -> Unit) (q : Unit -> Unit),
      (forall n : Nat, (tau^[n]) () = ()) /\ completionDepth tau q = 0) /\
    (exists (tau : DelayedState -> DelayedState) (q : DelayedState -> Bool),
      tau .zero = .one /\ 2 <= completionDepth tau q) := by
  classical
  constructor
  · refine ⟨longRunUpdate, longRunReadout, ?_, ?_⟩
    · intro n
      simp [longRunUpdate]
    · simp [completionDepth, distinguishingTime, completeItinerary,
        longRunUpdate, longRunReadout]
  · refine ⟨delayedUpdate, delayedReadout, rfl, ?_⟩
    let chosen := distinguishingTime delayedUpdate delayedReadout
      DelayedState.zero DelayedState.one
    have hseparates : exists n,
        completeItinerary delayedUpdate delayedReadout DelayedState.zero n ≠
          completeItinerary delayedUpdate delayedReadout DelayedState.one n := by
      exact ⟨2, by decide⟩
    have hchosen :
        completeItinerary delayedUpdate delayedReadout DelayedState.zero chosen ≠
          completeItinerary delayedUpdate delayedReadout DelayedState.one chosen := by
      simp only [chosen, distinguishingTime, dif_pos hseparates]
      exact Classical.choose_spec hseparates
    have hnotzero : chosen ≠ 0 := by
      intro hzero
      rw [hzero] at hchosen
      exact hchosen rfl
    have hnotone : chosen ≠ 1 := by
      intro hone
      rw [hone] at hchosen
      exact hchosen rfl
    have hchosen_ge : 2 <= chosen := by
      omega
    have hchosen_le : chosen <= completionDepth delayedUpdate delayedReadout := by
      exact Finset.le_sup (s := Finset.univ)
        (f := fun pair : DelayedState × DelayedState =>
          distinguishingTime delayedUpdate delayedReadout pair.1 pair.2)
        (Finset.mem_univ (DelayedState.zero, DelayedState.one))
    omega

example : (longRunUpdate^[100]) () = () := by
  rfl

#print axioms clock_time_does_not_determine_refinement_depth

end D5.S3.ObserverMemory.PredictionCertificates.ClockTimeVersusRefinementDepth
