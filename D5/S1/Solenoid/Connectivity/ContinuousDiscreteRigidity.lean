/- GID: D5/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity
   generality: G
   mirror-B: D5/B/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every continuous map from a connected space to a discrete space is constant. -/

import Mathlib.Topology.Connected.TotallyDisconnected

/- Library-search audit trail (2026-08-20):
   * Repository search found no theorem stating that every continuous map from a
     connected space to a discrete space is constant.
   * Pinned Mathlib contains the exact theorem `PreconnectedSpace.constant` in
     `Mathlib.Topology.Connected.TotallyDisconnected`; the proof below applies it
     directly after obtaining preconnectedness from the connected-space instance. -/

namespace D5.S1.Solenoid.Connectivity.ContinuousDiscreteRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every continuous map from a connected space to a discrete space is constant. -/
theorem continuous_map_to_discrete_is_constant
    {X Y : Type*} [TopologicalSpace X] [ConnectedSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y]
    (T : X → Y) (hT : Continuous T) :
    ∀ x y : X, T x = T y := by
  intro x y
  exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace X) hT

example : Unit := ()

example : ∀ x y : Unit, (fun _ : Unit => ()) x = (fun _ : Unit => ()) y := by
  letI : ConnectedSpace Unit :=
    { toPreconnectedSpace := ⟨Set.subsingleton_univ.isPreconnected⟩
      toNonempty := inferInstance }
  exact continuous_map_to_discrete_is_constant (fun _ : Unit => ()) continuous_const

#print axioms continuous_map_to_discrete_is_constant

end D5.S1.Solenoid.Connectivity.ContinuousDiscreteRigidity
