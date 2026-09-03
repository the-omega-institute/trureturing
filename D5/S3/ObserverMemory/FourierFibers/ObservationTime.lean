/- GID: D5/S3/ObserverMemory/FourierFibers/ObservationTime
   generality: G
   mirror-B: none(waiver:new-observer-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical separation time is the exact boundary at which a pair leaves the finite observation fiber. -/

import D5.S3.Observer.Separation.FiniteFutureCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.ObservationTime

open D5.S3.Observer.Separation.FiniteFutureCongruence

/-- Having no finite separating readout is exactly membership in the canonical
all-time hidden fiber. No second observation-time predicate is introduced. -/
theorem no_finite_separation_iff_infinite_future
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State) :
    (¬ ∃ depth,
      observedAt step readout depth left ≠
        observedAt step readout depth right) ↔
      (left, right) ∈ infiniteFutureRelation step readout := by
  constructor
  · intro h depth
    by_contra hdiff
    exact h ⟨depth, hdiff⟩
  · intro hfuture hseparated
    rcases hseparated with ⟨depth, hdiff⟩
    exact hdiff (hfuture depth)

/-- The repository's canonical `separationTime` is visibly separating whenever
such a finite readout exists. -/
theorem separation_time_visible
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : ∃ depth,
      observedAt step readout depth left ≠
        observedAt step readout depth right) :
    observedAt step readout
        (separationTime step readout (left, right)) left ≠
      observedAt step readout
        (separationTime step readout (left, right)) right := by
  classical
  simp only [separationTime, dif_pos hseparated]
  exact Nat.find_spec hseparated

/-- Every readout strictly before the canonical separation time still agrees. -/
theorem before_separation_time_hidden
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : ∃ depth,
      observedAt step readout depth left ≠
        observedAt step readout depth right)
    {earlier : ℕ}
    (hearlier : earlier < separationTime step readout (left, right)) :
    observedAt step readout earlier left =
      observedAt step readout earlier right := by
  classical
  have hearlierFind : earlier < Nat.find hseparated := by
    simpa only [separationTime, dif_pos hseparated] using hearlier
  by_contra hdiff
  exact (Nat.find_min hseparated hearlierFind) hdiff

/-- The canonical separation time has the exact first-visible semantics: the
pair differs there and agrees at every earlier dynamical readout. -/
theorem separation_time_first_visible_characterization
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : ∃ depth,
      observedAt step readout depth left ≠
        observedAt step readout depth right) :
    observedAt step readout
        (separationTime step readout (left, right)) left ≠
      observedAt step readout
        (separationTime step readout (left, right)) right ∧
    ∀ earlier < separationTime step readout (left, right),
      observedAt step readout earlier left =
        observedAt step readout earlier right := by
  exact ⟨separation_time_visible step readout left right hseparated,
    fun earlier hearlier =>
      before_separation_time_hidden step readout left right
        hseparated hearlier⟩

/-- For an eventually separated pair, finite-future fiber membership is
characterized exactly by horizons lying before the canonical separation time. -/
theorem finite_future_membership_iff_before_separation
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : ∃ depth,
      observedAt step readout depth left ≠
        observedAt step readout depth right)
    (horizon : ℕ) :
    (left, right) ∈ finiteFutureRelation step readout horizon ↔
      horizon < separationTime step readout (left, right) := by
  constructor
  · intro hfuture
    by_contra hnotBefore
    have hvisible :
        separationTime step readout (left, right) ≤ horizon :=
      Nat.le_of_not_gt hnotBefore
    exact separation_time_visible step readout left right hseparated
      (hfuture (separationTime step readout (left, right)) hvisible)
  · intro hbefore depth hdepth
    exact before_separation_time_hidden step readout left right hseparated
      (lt_of_le_of_lt hdepth hbefore)

#print axioms no_finite_separation_iff_infinite_future
#print axioms separation_time_visible
#print axioms before_separation_time_hidden
#print axioms separation_time_first_visible_characterization
#print axioms finite_future_membership_iff_before_separation

end D5.S3.ObserverMemory.FourierFibers.ObservationTime
