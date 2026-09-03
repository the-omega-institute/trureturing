/- GID: D5/S3/ObserverMemory/FourierFibers/ObservationTime
   generality: G
   mirror-B: none(waiver:new-observer-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical separation time is exactly the first dynamical readout at which a pair becomes visible. -/

import D5.S3.Observer.Separation.FiniteFutureCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.ObservationTime

open D5.S3.Observer.Separation.FiniteFutureCongruence

/-- A pair is eventually separated when some finite dynamical readout differs. -/
def EventuallySeparated {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State) : Prop :=
  ∃ depth,
    observedAt step readout depth left ≠
      observedAt step readout depth right

/-- A depth is first-visible when the pair differs there and agreed at every
earlier dynamical readout. -/
def FirstVisibleAt {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State) (depth : ℕ) : Prop :=
  observedAt step readout depth left ≠
      observedAt step readout depth right ∧
    ∀ earlier < depth,
      observedAt step readout earlier left =
        observedAt step readout earlier right

/-- Never being separated is exactly membership in the all-time hidden fiber. -/
theorem not_eventually_separated_iff_infinite_future
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State) :
    ¬ EventuallySeparated step readout left right ↔
      (left, right) ∈ infiniteFutureRelation step readout := by
  constructor
  · intro h depth
    by_contra hdiff
    exact h ⟨depth, hdiff⟩
  · intro hfuture hseparated
    rcases hseparated with ⟨depth, hdiff⟩
    exact hdiff (hfuture depth)

/-- The repository's canonical `separationTime` is a visible depth whenever
the pair is eventually separated. -/
theorem separation_time_visible
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : EventuallySeparated step readout left right) :
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
    (hseparated : EventuallySeparated step readout left right)
    {earlier : ℕ}
    (hearlier : earlier < separationTime step readout (left, right)) :
    observedAt step readout earlier left =
      observedAt step readout earlier right := by
  classical
  have hearlierFind : earlier < Nat.find hseparated := by
    simpa only [separationTime, dif_pos hseparated] using hearlier
  by_contra hdiff
  exact (Nat.find_min hseparated hearlierFind) hdiff

/-- The canonical separation time satisfies the first-visible specification. -/
theorem separation_time_is_first_visible
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : EventuallySeparated step readout left right) :
    FirstVisibleAt step readout left right
      (separationTime step readout (left, right)) := by
  exact ⟨separation_time_visible step readout left right hseparated,
    fun earlier hearlier =>
      before_separation_time_hidden step readout left right
        hseparated hearlier⟩

/-- A first-visible depth is unique. -/
theorem first_visible_at_unique
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State) {first second : ℕ}
    (hfirst : FirstVisibleAt step readout left right first)
    (hsecond : FirstVisibleAt step readout left right second) :
    first = second := by
  apply le_antisymm
  · by_contra hnot
    have hlt : second < first := Nat.lt_of_not_ge hnot
    exact hsecond.1 (hfirst.2 second hlt)
  · by_contra hnot
    have hlt : first < second := Nat.lt_of_not_ge hnot
    exact hfirst.1 (hsecond.2 first hlt)

/-- Any independently supplied first-visible depth equals the canonical
repository separation time. -/
theorem separation_time_eq_of_first_visible
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : EventuallySeparated step readout left right)
    {depth : ℕ}
    (hdepth : FirstVisibleAt step readout left right depth) :
    separationTime step readout (left, right) = depth :=
  first_visible_at_unique step readout left right
    (separation_time_is_first_visible step readout left right hseparated)
    hdepth

/-- Before the first visible time, the pair remains in every finite observation
fiber whose horizon is strictly earlier. -/
theorem before_separation_in_finite_future
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : EventuallySeparated step readout left right)
    {horizon : ℕ}
    (hbefore : horizon < separationTime step readout (left, right)) :
    (left, right) ∈ finiteFutureRelation step readout horizon := by
  intro depth hdepth
  exact before_separation_time_hidden step readout left right hseparated
    (lt_of_le_of_lt hdepth hbefore)

/-- At and beyond the first visible time, the pair is excluded from the finite
observation fiber. -/
theorem at_or_after_separation_not_in_finite_future
    {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State)
    (hseparated : EventuallySeparated step readout left right)
    {horizon : ℕ}
    (hvisible : separationTime step readout (left, right) ≤ horizon) :
    (left, right) ∉ finiteFutureRelation step readout horizon := by
  intro hfuture
  exact separation_time_visible step readout left right hseparated
    (hfuture (separationTime step readout (left, right)) hvisible)

#print axioms not_eventually_separated_iff_infinite_future
#print axioms separation_time_is_first_visible
#print axioms first_visible_at_unique
#print axioms separation_time_eq_of_first_visible
#print axioms before_separation_in_finite_future
#print axioms at_or_after_separation_not_in_finite_future

end D5.S3.ObserverMemory.FourierFibers.ObservationTime
