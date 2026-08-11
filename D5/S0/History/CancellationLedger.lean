/- GID: D5/S0/History/CancellationLedger
   generality: G
   mirror-B: D5/B/S0/History/CancellationLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A referenced cancellation preserves the old ledger and appends one entry. -/

import D5.S0.History.HistoryCarrier

namespace D5.S0.History.CancellationLedger

open D5.S0.History

/- Provenance: thin honest wrapper over pinned mathlib's free-monoid
   membership and length laws (`FreeMonoid.mem_mul`, `FreeMonoid.length_mul`,
   `FreeMonoid.length_of`, and `List.get_mem`). -/

/-- A cancellation carries both a valid reference into the existing ledger
and the compensating event that will be recorded after it. -/
structure CancellationEntry (history : EventHistory) where
  target : Fin history.length
  compensatingEvent : Event

/-- The earlier event named by a cancellation entry. -/
def cancelledEvent (history : EventHistory) (entry : CancellationEntry history) : Event :=
  history.toList.get entry.target

/-- One event ledger extends another when the earlier ledger is a left factor. -/
def IsLedgerPrefix (earlier later : EventHistory) : Prop :=
  ∃ suffix, later = earlier * suffix

/-- Record a cancellation as a new event without rewriting the old ledger. -/
def recordCancellation (history : EventHistory) (entry : CancellationEntry history) :
    EventHistory :=
  generate history entry.compensatingEvent

/-- Recording a cancellation is append-only: the old ledger is a prefix,
the referenced event remains present, and the new ledger has exactly one
additional entry. -/
theorem record_cancellation_is_append_only
    (history : EventHistory) (entry : CancellationEntry history) :
    IsLedgerPrefix history (recordCancellation history entry) ∧
      cancelledEvent history entry ∈ recordCancellation history entry ∧
      (recordCancellation history entry).length = history.length + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨FreeMonoid.of entry.compensatingEvent, rfl⟩
  · rw [recordCancellation, generate, FreeMonoid.mem_mul]
    left
    exact List.get_mem history.toList entry.target
  · simp [recordCancellation, generate]

end D5.S0.History.CancellationLedger
