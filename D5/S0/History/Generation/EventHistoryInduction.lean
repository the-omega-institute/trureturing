/- GID: D5/S0/History/Generation/EventHistoryInduction
   generality: G
   mirror-B: D5/B/S0/History/Generation/EventHistoryInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Event-history properties follow from empty and one-event generation cases. -/

import D5.S0.History.HistoryCarrier

namespace D5.S0.History.Generation

/-- A property of event histories holds universally when it holds for the empty history
and is preserved whenever one event is appended. -/
theorem event_history_induction
    (P : EventHistory → Prop)
    (empty : P 1)
    (step : ∀ (h : EventHistory) (u : Event), P h → P (generate h u)) :
    ∀ h : EventHistory, P h := by
  intro h
  have reversed : P (FreeMonoid.reverse (FreeMonoid.reverse h)) := by
    refine FreeMonoid.inductionOn' (FreeMonoid.reverse h) ?_ ?_
    · change P 1
      exact empty
    · intro u tail ih
      rw [FreeMonoid.reverse_mul, FreeMonoid.reverse_of]
      simpa [generate] using step (FreeMonoid.reverse tail) u ih
  simpa using reversed

end D5.S0.History.Generation
