/- GID: D5/S3/ConceptDynamics/Topology/ConnectedDiscreteNamingDiscontinuity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/ConnectedDiscreteNamingDiscontinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Connected discrete naming is constant, and nonconstant naming is discontinuous. -/

import D5.S1.Solenoid.Connectivity.ContinuousDiscreteRigidity

/- Library-search audit trail (2026-09-02):
   * The exact forward clause is owned by
     `ContinuousDiscreteRigidity.continuous_map_to_discrete_is_constant` and is
     applied directly below.
   * Pinned Mathlib supplies the underlying exact theorem
     `PreconnectedSpace.constant` in
     `Mathlib.Topology.Connected.TotallyDisconnected`.
   * Name and body-shape searches found no theorem on the same simple carrier
     that publicly conjoins the forward clause with its nonconstant-map
     contrapositive. `ContinuousHardClassificationObstruction` has a broader
     factorized-classifier carrier and four obstruction alternatives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.ConnectedDiscreteNamingDiscontinuity

open D5.S1.Solenoid.Connectivity.ContinuousDiscreteRigidity

/-- A continuous discrete name on a connected space is constant. Equivalently,
a witnessed nonconstant discrete name on that carrier cannot be continuous. -/
theorem connected_discrete_naming_discontinuity
    {X N : Type*} [TopologicalSpace X] [ConnectedSpace X]
    [TopologicalSpace N] [DiscreteTopology N]
    (name : X -> N) :
    (Continuous name -> forall first second : X, name first = name second) ∧
      ((exists first second : X, name first ≠ name second) ->
        ¬Continuous name) := by
  have constant_if_continuous :
      Continuous name -> forall first second : X, name first = name second := by
    intro continuous_name
    exact continuous_map_to_discrete_is_constant name continuous_name
  constructor
  · exact constant_if_continuous
  · rintro ⟨first, second, values_differ⟩ continuous_name
    exact values_differ (constant_if_continuous continuous_name first second)

#print axioms connected_discrete_naming_discontinuity

end D5.S3.ConceptDynamics.Topology.ConnectedDiscreteNamingDiscontinuity
