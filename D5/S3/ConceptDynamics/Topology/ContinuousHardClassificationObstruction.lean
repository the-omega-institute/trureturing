/- GID: D5/S3/ConceptDynamics/Topology/ContinuousHardClassificationObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/ContinuousHardClassificationObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonconstant discrete classification forces a topological or continuity obstruction. -/

import D5.S1.Solenoid.Connectivity.ContinuousDiscreteRigidity

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit
     `ContinuousDiscreteRigidity.continuous_map_to_discrete_is_constant` is already
     frozen and is applied directly to the realized representation image below.
   * Its pinned-Mathlib source uses the exact theorem `PreconnectedSpace.constant`.
     The supporting exact hit `isConnected_range` transports connectedness of the
     object domain through the continuous representation in the obstruction direction.
   * Searches across D5, Blueprint, accepted freezes, and digestion receipts found no
     theorem packaging the factorized classifier with all four public obstruction
     alternatives. External `loogle` and `leansearch` executables were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.ContinuousHardClassificationObstruction

open D5.S1.Solenoid.Connectivity.ContinuousDiscreteRigidity

/-- A classifier that continuously factors through a connected realized representation
into a discrete output is constant. Consequently, a witnessed nonconstant classifier
forces a disconnected realized representation, a discontinuous decoder, a nondiscrete
output, or a disconnected object domain. -/
theorem continuous_hard_classification_obstruction
    {X B Y : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace Y]
    (representation : X -> B) (decoder : B -> Y) (classifier : X -> Y)
    (classifier_factors : classifier = decoder ∘ representation)
    (representation_continuous : Continuous representation) :
    (Continuous decoder ->
      IsConnected (Set.range representation) ->
      DiscreteTopology Y ->
      forall first second : X, classifier first = classifier second) ∧
    ((exists first second : X, classifier first ≠ classifier second) ->
      ¬IsConnected (Set.range representation) ∨
        ¬Continuous decoder ∨
        ¬DiscreteTopology Y ∨
        ¬IsConnected (Set.univ : Set X)) := by
  have constant_on_connected_representation :
      Continuous decoder ->
        IsConnected (Set.range representation) ->
        DiscreteTopology Y ->
        forall first second : X, classifier first = classifier second := by
    intro decoder_continuous range_connected output_discrete first second
    letI : DiscreteTopology Y := output_discrete
    letI : ConnectedSpace (Set.range representation) :=
      Subtype.connectedSpace range_connected
    have restricted_decoder_constant :=
      continuous_map_to_discrete_is_constant
        (fun value : Set.range representation => decoder value.1)
        (decoder_continuous.comp continuous_subtype_val)
        (⟨representation first, ⟨first, rfl⟩⟩ : Set.range representation)
        (⟨representation second, ⟨second, rfl⟩⟩ : Set.range representation)
    simpa only [classifier_factors, Function.comp_apply] using
      restricted_decoder_constant
  constructor
  · exact constant_on_connected_representation
  · rintro ⟨first, second, values_differ⟩
    by_cases domain_connected : IsConnected (Set.univ : Set X)
    · letI : ConnectedSpace X := connectedSpace_iff_univ.mpr domain_connected
      have range_connected : IsConnected (Set.range representation) :=
        isConnected_range representation_continuous
      by_cases decoder_continuous : Continuous decoder
      · by_cases output_discrete : DiscreteTopology Y
        · exact (values_differ
            (constant_on_connected_representation decoder_continuous range_connected
              output_discrete first second)).elim
        · exact Or.inr (Or.inr (Or.inl output_discrete))
      · exact Or.inr (Or.inl decoder_continuous)
    · exact Or.inr (Or.inr (Or.inr domain_connected))

#print axioms continuous_hard_classification_obstruction

end D5.S3.ConceptDynamics.Topology.ContinuousHardClassificationObstruction
