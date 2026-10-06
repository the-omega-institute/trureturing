/- GID: D5/S1/Digit/Infinite/SevenCycleCollisionResult
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCollisionResult
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/Infinite/SevenCycleSeparationRefutation.claim; result=D5/S1/Digit/Infinite/SevenCycleCollisionResult.result; claim=D5/S1/Digit/Infinite/SevenCycleSeparationRefutation.claim
   digest: A seven-cycle actual singleton rival refutes unconditional finite-future separation. -/

import D5.S1.Digit.Infinite.SevenCycleOriginalGraph
import D5.S1.Digit.Infinite.SevenCycleActualCollision

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCollisionResult

open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleCollisionData
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleOriginalGraph
open private budget_bounds from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private original_parameters rival_qualified from D5.S1.Digit.Infinite.SevenCycleOriginalGraph
open private actual_collision from D5.S1.Digit.Infinite.SevenCycleActualCollision

/-- The universal unconditional finite-future separation assertion is false. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨n, hn⟩ := hc budget denominator 100 budget_bounds.2.2.1 budget_bounds.2.2.2
    original_parameters (source false) rival_qualified
  have hd : threeLabel ≠ nullLabel := by
    intro h
    have he := congrArg (fun l : Label => l.val 1) h
    norm_num [threeLabel, nullLabel] at he
  obtain ⟨hy1, hy2, hpersist⟩ := actual_collision
  have h := hn false threeLabel nullLabel 1 2
    (by simp [lawful, outgoing, threeLabel]) (by simp [lawful, outgoing, nullLabel]) hd hy1 hy2
  have hm := hpersist n
  rw [h] at hm
  exact Set.notMem_empty _ hm

end D5.S1.Digit.Infinite.SevenCycleCollisionResult
