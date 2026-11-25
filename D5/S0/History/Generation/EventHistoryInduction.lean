/- GID: D5/S0/History/Generation/EventHistoryInduction
   generality: G
   mirror-B: D5/B/S0/History/Generation/EventHistoryInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Event-history properties follow from empty and one-event generation cases. -/

module
prelude
public import OmegaMath.Data.SnocList

namespace D5.S0.History.Generation

open Omega

/-- A property of finite event histories follows from the empty history and
preservation under appending one event. -/
public theorem event_history_induction
    {Event : Type u} (P : SnocList Event → Prop)
    (empty : P .empty)
    (step : ∀ history event, P history → P (history.pushBack event)) :
    ∀ history, P history :=
  SnocList.rec (motive := fun history => P history) empty
    (fun history last previous => step history (last True.intro) previous)

end D5.S0.History.Generation
