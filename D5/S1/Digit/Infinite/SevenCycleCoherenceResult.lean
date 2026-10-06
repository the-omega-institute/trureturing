/- GID: D5/S1/Digit/Infinite/SevenCycleCoherenceResult
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCoherenceResult
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/Infinite/SevenCycleCoherenceRefutation.claim; result=D5/S1/Digit/Infinite/SevenCycleCoherenceResult.result; claim=D5/S1/Digit/Infinite/SevenCycleCoherenceRefutation.claim
   digest: An actual coherent return SCC does not require finite future separation. -/

import D5.S1.Digit.Infinite.SevenCyclePairedGraph
import D5.S1.Digit.Infinite.SevenCycleCollisionResult

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCoherenceResult

open D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation
open private source budget budget_bounds from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private denominator original_parameters rival_qualified
  from D5.S1.Digit.Infinite.SevenCycleOriginalGraph
open private counterexample from D5.S1.Digit.Infinite.SevenCycleCollisionResult
open private actual_coherent_rival from D5.S1.Digit.Infinite.SevenCyclePairedGraph

/-- The necessity assertion fails in the original complete paired graph. -/
theorem result : ¬ claim := by
  intro hc
  exact counterexample (hc budget denominator 100 budget_bounds.2.2.1
    budget_bounds.2.2.2 original_parameters (source false) rival_qualified actual_coherent_rival)

end D5.S1.Digit.Infinite.SevenCycleCoherenceResult
