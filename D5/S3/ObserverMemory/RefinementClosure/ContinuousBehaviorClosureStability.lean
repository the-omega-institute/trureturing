/- GID: D5/S3/ObserverMemory/RefinementClosure/ContinuousBehaviorClosureStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/ContinuousBehaviorClosureStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A continuous action preserving realizable behaviors also preserves their closure. -/

import Mathlib.Topology.Continuous

/- Library-search audit trail (2026-08-28):
   * Exact pinned-Mathlib hit `Set.MapsTo.closure` states that a continuous map
     sends the closure of its source set into the closure of its target set.
     It is applied directly with the same realizable set on both sides.
   * Repository searches under ObserverMemory and Observer found no frozen D5
     theorem with the same continuous self-action and closure-invariance statement.
   * No new definition or family primitive is introduced. -/

namespace D5.S3.ObserverMemory.RefinementClosure.ContinuousBehaviorClosureStability

open Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A continuous action that preserves the realizable behavior set preserves
its topological closure as well. -/
theorem continuous_dynamics_preserves_behavior_closure
    {B : Type*} [TopologicalSpace B]
    (action : B -> B) (realizable : Set B)
    (continuousAction : Continuous action)
    (preservesRealizable : Set.MapsTo action realizable realizable) :
    Set.MapsTo action (closure realizable) (closure realizable) :=
  preservesRealizable.closure continuousAction

#print axioms continuous_dynamics_preserves_behavior_closure

end D5.S3.ObserverMemory.RefinementClosure.ContinuousBehaviorClosureStability
