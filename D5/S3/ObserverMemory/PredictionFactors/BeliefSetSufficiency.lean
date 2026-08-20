/- GID: D5/S3/ObserverMemory/PredictionFactors/BeliefSetSufficiency
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/BeliefSetSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal compatible belief sets determine equal future observation trajectories. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Data.List.Infix

/- Library-search audit trail (2026-08-21):
   * Exact repository hits `runWord` and `controlledBehavior` provide the
     canonical controlled-state semantics and are imported and used below.
   * Exact pinned-Mathlib hit `List.inits` supplies every prefix of a future
     action word and is applied in the observation-trajectory construction.
   * Pinned Mathlib also provides generic `Set.image_congr` and
     `Set.image_image`; neither packages compatible histories, transition-path
     semantics, or belief sufficiency.
   * Searches of D5, pinned Mathlib, the active branch, and `origin/dev` for
     compatible-belief sufficiency found no equal or stronger theorem.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionFactors.BeliefSetSufficiency

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- Update a compatible-state set by one observed action transition. -/
def updateBelief {X U O : Type*} (update : U -> X -> X) (observe : X -> O)
    (current : Set X) (step : U × O) : Set X :=
  {next | exists state, state ∈ current /\
    update step.1 state = next /\ observe next = step.2}

/-- Repeatedly apply the source's one-step belief update. -/
def compatibleBeliefFrom {X U O : Type*} (update : U -> X -> X)
    (observe : X -> O) : Set X -> List (U × O) -> Set X
  | current, [] => current
  | current, step :: history =>
      compatibleBeliefFrom update observe
        (updateBelief update observe current step) history

/-- Hidden states compatible with an initial observation and a chronological
list of subsequent action-observation pairs. -/
def compatibleBelief {X U O : Type*} (update : U -> X -> X)
    (observe : X -> O) (initialObservation : O)
    (history : List (U × O)) : Set X :=
  compatibleBeliefFrom update observe
    {state | observe state = initialObservation} history

/-- A hidden start state reaches a hidden final state by following every
observed action transition in a concrete history. -/
def followsObservedActions {X U O : Type*} (update : U -> X -> X)
    (observe : X -> O) : List (U × O) -> X -> X -> Prop
  | [], start, final => final = start
  | step :: history, start, final =>
      exists next,
        update step.1 start = next /\ observe next = step.2 /\
          followsObservedActions update observe history next final

/-- The observation trajectory along a future action word, including the
current readout, is the canonical controlled behavior on every word prefix. -/
def observationTrajectory {X U O : Type*} (update : U -> X -> X)
    (observe : X -> O) (futureActions : List U) (state : X) : List O :=
  futureActions.inits.map (controlledBehavior update observe state)

/-- Possible future observation trajectories constructed directly from the
hidden transition paths compatible with a concrete history. -/
def possibleObservationTrajectories {X U O : Type*}
    (update : U -> X -> X) (observe : X -> O)
    (initialObservation : O) (history : List (U × O))
    (futureActions : List U) : Set (List O) :=
  {trajectory | exists start final,
    observe start = initialObservation /\
      followsObservedActions update observe history start final /\
      observationTrajectory update observe futureActions final = trajectory}

private theorem mem_compatibleBeliefFrom_iff
    {X U O : Type*} (update : U -> X -> X) (observe : X -> O)
    (current : Set X) (history : List (U × O)) (final : X) :
    final ∈ compatibleBeliefFrom update observe current history <->
      exists start, start ∈ current /\
        followsObservedActions update observe history start final := by
  induction history generalizing current with
  | nil =>
      simp [compatibleBeliefFrom, followsObservedActions]
  | cons step history ih =>
      rw [compatibleBeliefFrom, ih]
      constructor
      · rintro ⟨next, ⟨start, hcurrent, hupdate, hobserve⟩, hfollow⟩
        exact ⟨start, hcurrent, next, hupdate, hobserve, hfollow⟩
      · rintro ⟨start, hcurrent, next, hupdate, hobserve, hfollow⟩
        exact ⟨next, ⟨start, hcurrent, hupdate, hobserve⟩, hfollow⟩

private theorem mem_compatibleBelief_iff
    {X U O : Type*} (update : U -> X -> X) (observe : X -> O)
    (initialObservation : O) (history : List (U × O)) (final : X) :
    final ∈ compatibleBelief update observe initialObservation history <->
      exists start, observe start = initialObservation /\
        followsObservedActions update observe history start final := by
  simpa [compatibleBelief] using
    (mem_compatibleBeliefFrom_iff update observe
      {state | observe state = initialObservation} history final)

/-- Histories with the same recursively constructed compatible-state set have
the same set of possible observation trajectories for every future action
word. Thus the future prediction depends on the belief set, not on which
history generated it. -/
theorem belief_set_sufficiency
    {X U O : Type*} (update : U -> X -> X) (observe : X -> O)
    (initialObservationFirst initialObservationSecond : O)
    (historyFirst historySecond : List (U × O))
    (sameBelief :
      compatibleBelief update observe initialObservationFirst historyFirst =
        compatibleBelief update observe initialObservationSecond historySecond) :
    forall futureActions : List U,
      possibleObservationTrajectories update observe
          initialObservationFirst historyFirst futureActions =
        possibleObservationTrajectories update observe
          initialObservationSecond historySecond futureActions := by
  intro futureActions
  ext trajectory
  change
    (exists start final,
      observe start = initialObservationFirst /\
        followsObservedActions update observe historyFirst start final /\
        observationTrajectory update observe futureActions final = trajectory) <->
    (exists start final,
      observe start = initialObservationSecond /\
        followsObservedActions update observe historySecond start final /\
        observationTrajectory update observe futureActions final = trajectory)
  constructor
  · rintro ⟨start, final, hobserve, hfollow, htrajectory⟩
    have hfirst :
        final ∈ compatibleBelief update observe
          initialObservationFirst historyFirst :=
      (mem_compatibleBelief_iff update observe
        initialObservationFirst historyFirst final).2
        ⟨start, hobserve, hfollow⟩
    have hsecond :
        final ∈ compatibleBelief update observe
          initialObservationSecond historySecond := by
      rw [← sameBelief]
      exact hfirst
    rcases (mem_compatibleBelief_iff update observe
      initialObservationSecond historySecond final).1 hsecond with
      ⟨secondStart, hsecondObserve, hsecondFollow⟩
    exact ⟨secondStart, final, hsecondObserve, hsecondFollow, htrajectory⟩
  · rintro ⟨start, final, hobserve, hfollow, htrajectory⟩
    have hsecond :
        final ∈ compatibleBelief update observe
          initialObservationSecond historySecond :=
      (mem_compatibleBelief_iff update observe
        initialObservationSecond historySecond final).2
        ⟨start, hobserve, hfollow⟩
    have hfirst :
        final ∈ compatibleBelief update observe
          initialObservationFirst historyFirst := by
      rw [sameBelief]
      exact hsecond
    rcases (mem_compatibleBelief_iff update observe
      initialObservationFirst historyFirst final).1 hfirst with
      ⟨firstStart, hfirstObserve, hfirstFollow⟩
    exact ⟨firstStart, final, hfirstObserve, hfirstFollow, htrajectory⟩

/-- Distinct Boolean histories can satisfy the equal-belief premise. -/
example :
    ([] : List (Unit × Bool)) != [((), false)] /\
      compatibleBelief (fun _ : Unit => id) id false [] =
        compatibleBelief (fun _ : Unit => id) id false [((), false)] := by
  constructor
  · simp
  · ext state
    simp [compatibleBelief, compatibleBeliefFrom, updateBelief]

/-- The hidden-state domain used by the premise witness is inhabited. -/
example : Bool := false

#print axioms belief_set_sufficiency

end D5.S3.ObserverMemory.PredictionFactors.BeliefSetSufficiency
