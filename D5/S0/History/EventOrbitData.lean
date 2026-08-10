/- GID: D5/S0/History/EventOrbitData
   generality: G
   mirror-B: D5/B/S0/History/EventOrbitData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The event sequence uniquely determines the state orbit, and the history component records that sequence step by step. -/

import D5.S0.History.HistoryCarrier

namespace D5.S0.History.EventOrbitData

open D5.S0.History

def eventPrefix (events : Nat -> Event) : Nat -> EventHistory
  | 0 => 1
  | n + 1 => generate (eventPrefix events n) (events n)

theorem event_sequence_determines_orbit_and_history
    {State : Type*} (step : State -> Event -> State)
    (history : State -> EventHistory) (initial : State) (events : Nat -> Event)
    (left right : Nat -> State)
    (left_zero : left 0 = initial) (right_zero : right 0 = initial)
    (left_step : forall n, left (n + 1) = step (left n) (events n))
    (right_step : forall n, right (n + 1) = step (right n) (events n))
    (history_zero : history initial = 1)
    (history_step : forall state event,
      history (step state event) = generate (history state) event) :
    left = right ∧ forall n, history (left n) = eventPrefix events n := by
  constructor
  · funext n
    induction n with
    | zero => exact left_zero.trans right_zero.symm
    | succ n ih => rw [left_step, right_step, ih]
  · intro n
    induction n with
    | zero => simpa [eventPrefix, left_zero] using history_zero
    | succ n ih => rw [left_step, history_step, eventPrefix, ih]

end D5.S0.History.EventOrbitData
