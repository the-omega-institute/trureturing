/- GID: D5/S0/History/EventOrbitData
   generality: G
   mirror-B: D5/B/S0/History/EventOrbitData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The event sequence uniquely determines the state orbit, and the history component records that sequence step by step. -/

import D5.S0.History.HistoryCarrier
import OmegaMath.Data.SnocList

namespace D5.S0.History.EventOrbitData

open D5.S0.History

def eventPrefix (events : Nat -> Event) : Nat -> EventHistory
  | 0 => 1
  | n + 1 => generate (eventPrefix events n) (events n)

/-- The finite prefix of an event sequence in the strict list representation. -/
noncomputable def strictEventPrefix {EventType : Type v}
    (events : Omega.Nat → EventType) : Omega.Nat → Omega.SnocList EventType :=
  Omega.Nat.rec .empty (fun index history => history.pushBack (events index))

/-- The recurrence determines the orbit at every index and records its event prefix. -/
theorem event_sequence_determines_orbit_and_history
    {State : Type u} {EventType : Type v} (step : State → EventType → State)
    (history : State → Omega.SnocList EventType) (initial : State) (events : Omega.Nat → EventType)
    (left right : Omega.Nat → State)
    (leftZero : Omega.Eq (left .zero) initial) (rightZero : Omega.Eq (right .zero) initial)
    (leftStep : ∀ n, Omega.Eq (left n.succ) (step (left n) (events n)))
    (rightStep : ∀ n, Omega.Eq (right n.succ) (step (right n) (events n)))
    (historyZero : Omega.Eq (history initial) .empty)
    (historyStep : ∀ state event,
      Omega.Eq (history (step state event)) ((history state).pushBack event)) :
    Omega.And (∀ n, Omega.Eq (left n) (right n))
      (∀ n, Omega.Eq (history (left n)) (strictEventPrefix events n)) :=
  Omega.And.intro
    (Omega.Nat.rec (motive := fun n => Omega.Eq (left n) (right n))
      (leftZero.trans rightZero.symm)
      (fun n previous => (leftStep n).trans
        ((Omega.congrArg (fun state => step state (events n)) previous).trans (rightStep n).symm)))
    (Omega.Nat.rec (motive := fun n => Omega.Eq (history (left n)) (strictEventPrefix events n))
      ((Omega.congrArg history leftZero).trans historyZero)
      (fun n previous => (Omega.congrArg history (leftStep n)).trans
        ((historyStep (left n) (events n)).trans
          (Omega.congrArg (fun prefixHistory => prefixHistory.pushBack (events n)) previous))))

end D5.S0.History.EventOrbitData
