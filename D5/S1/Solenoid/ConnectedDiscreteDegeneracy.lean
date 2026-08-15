/- GID: D5/S1/Solenoid/ConnectedDiscreteDegeneracy
   generality: G
   mirror-B: D5/B/S1/Solenoid/ConnectedDiscreteDegeneracy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty connected discrete topological space has exactly one point. -/

import Mathlib.Topology.Separation.Connected

/- Library-search audit trail (2026-08-15):
   * Loogle's overconstrained connected/discrete query found no result; the exact-name query
     `PreconnectedSpace.trivial_of_discrete` found the pinned-Mathlib theorem used below.
   * LeanSearch's natural-language query for a connected discrete space having exactly one
     point returned `PreconnectedSpace.trivial_of_discrete` as its top result; its exact-name
     query returned the same theorem.
   * Repository searches found no duplicate theorem. The related
     `D5.S3.Arith.HiddenFiberRigidity.hidden_fiber_rigidity` concerns continuous maps into a
     profinite fiber and does not state this claim. -/

namespace D5.S1.Solenoid.ConnectedDiscreteDegeneracy

/-- A connected discrete topological space has exactly one point. -/
theorem connected_discrete_has_unique_point
    (X : Type*) (topology : TopologicalSpace X)
    (connected : @ConnectedSpace X topology)
    (discrete : @DiscreteTopology X topology) :
    ∃ x : X, ∀ y : X, y = x := by
  letI : TopologicalSpace X := topology
  letI : ConnectedSpace X := connected
  letI : DiscreteTopology X := discrete
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  letI : Subsingleton X := PreconnectedSpace.trivial_of_discrete
  exact ⟨x, fun y => Subsingleton.elim y x⟩

example : TopologicalSpace Unit := inferInstance

example : ConnectedSpace Unit where
  toPreconnectedSpace := ⟨Set.subsingleton_univ.isPreconnected⟩
  toNonempty := inferInstance

example : DiscreteTopology Unit := inferInstance

example : Unit := ()

example : ∃ x : Unit, ∀ y : Unit, y = x := by
  letI : ConnectedSpace Unit :=
    { toPreconnectedSpace := ⟨Set.subsingleton_univ.isPreconnected⟩
      toNonempty := inferInstance }
  exact connected_discrete_has_unique_point Unit inferInstance inferInstance inferInstance

#print axioms connected_discrete_has_unique_point

end D5.S1.Solenoid.ConnectedDiscreteDegeneracy
