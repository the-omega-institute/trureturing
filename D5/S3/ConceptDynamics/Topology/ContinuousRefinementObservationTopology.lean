/- GID: D5/S3/ConceptDynamics/Topology/ContinuousRefinementObservationTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/ContinuousRefinementObservationTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous refinement makes the observation topology finer. -/

import Mathlib.Topology.Order

/- Library-search audit trail (2026-08-25):
   * Repository searches for observation topologies, induced topologies, and
     continuous refinement found no accepted theorem stating this general result.
   * The nearby `partitionTopology` is restricted to a discrete output topology.
   * Pinned Mathlib provides the exact component laws `Continuous.le_induced`,
     `induced_mono`, and `induced_compose`; they are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.ContinuousRefinementObservationTopology

/-- If a coarse readout continuously factors through a refined readout, every set
open in the coarse readout's induced observation topology is open in the refined
readout's induced observation topology. -/
theorem continuous_refinement_observation_topology
    {X CoarseValue RefinedValue : Type*}
    [TopologicalSpace CoarseValue] [TopologicalSpace RefinedValue]
    (coarse : X -> CoarseValue) (refined : X -> RefinedValue)
    (projection : RefinedValue -> CoarseValue)
    (factorization : coarse = projection ∘ refined)
    (projection_continuous : Continuous projection) :
    forall states : Set X,
      @IsOpen X
          (TopologicalSpace.induced coarse
            (inferInstance : TopologicalSpace CoarseValue)) states ->
        @IsOpen X
          (TopologicalSpace.induced refined
            (inferInstance : TopologicalSpace RefinedValue)) states := by
  intro states states_open
  have topology_order :
      TopologicalSpace.induced refined
          (inferInstance : TopologicalSpace RefinedValue) <=
        TopologicalSpace.induced coarse
          (inferInstance : TopologicalSpace CoarseValue) := by
    rw [factorization, <- induced_compose]
    exact induced_mono projection_continuous.le_induced
  exact topology_order states states_open

/-- The identity refinement on `Bool` witnesses simultaneous satisfiability of
the factorization and continuity hypotheses. -/
example :
    (fun value : Bool => value) =
        (fun value : Bool => value) ∘ (fun value : Bool => value) ∧
      Continuous (fun value : Bool => value) := by
  exact ⟨rfl, continuous_id⟩

example : Bool := false

#print axioms continuous_refinement_observation_topology

end D5.S3.ConceptDynamics.Topology.ContinuousRefinementObservationTopology
