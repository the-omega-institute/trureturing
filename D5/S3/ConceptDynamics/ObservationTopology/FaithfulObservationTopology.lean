/- GID: D5/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Injective observations induce discrete topology and preserve catalog escapes. -/

import D5.S3.ConceptDynamics.ObservationTopology.EscapeUnderObservation
import D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.FaithfulObservationTopology

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.ObservationTopology.EscapeUnderObservation

/-- The identity readout induces the discrete topology. -/
theorem partitionTopology_id_eq_discrete {X : Type*} :
    partitionTopology (id : Concept X X) = (⊥ : TopologicalSpace X) := by
  apply TopologicalSpace.ext_iff.mpr
  intro set
  constructor
  · intro _setOpen
    letI : TopologicalSpace X := ⊥
    letI : DiscreteTopology X := ⟨rfl⟩
    exact isOpen_discrete _
  · intro _setOpen
    letI : TopologicalSpace X := ⊥
    letI : DiscreteTopology X := ⟨rfl⟩
    change @IsOpen X
      (TopologicalSpace.induced (show X -> X from id) ⊥) set
    rw [isOpen_induced_iff]
    exact ⟨set, isOpen_discrete _, by ext x; rfl⟩

/-- A readout is faithful exactly when it induces the discrete partition
topology on its source. -/
theorem partitionTopology_eq_discrete_iff_injective
    {X Observation : Type*} (observe : Concept X Observation) :
    partitionTopology observe = (⊥ : TopologicalSpace X) ↔
      Function.Injective observe := by
  constructor
  · intro topologyDiscrete x y sameObserved
    have observedInseparable :
        @Inseparable X (partitionTopology observe) x y :=
      (partition_inseparable_iff_kernel observe x y).2 sameObserved
    have discreteInseparable :
        @Inseparable X (⊥ : TopologicalSpace X) x y := by
      exact topologyDiscrete ▸ observedInseparable
    letI : TopologicalSpace X := ⊥
    letI : DiscreteTopology X := ⟨rfl⟩
    exact discreteInseparable.eq
  · intro injective
    calc
      partitionTopology observe = partitionTopology (id : Concept X X) := by
        apply partitionTopology_eq_of_kernel_iff
        intro x y
        exact ⟨fun sameObserved => injective sameObserved,
          fun sameIdentity => congrArg observe sameIdentity⟩
      _ = (⊥ : TopologicalSpace X) := partitionTopology_id_eq_discrete

/-- Topological faithfulness is exactly preservation of every one-row catalog
escape, on every inhabited catalog input. -/
theorem discrete_partition_iff_preserves_unit_catalog_escape
    {Input Output Observation : Type*} [Nonempty Input]
    (observe : Output → Observation) :
    partitionTopology observe = (⊥ : TopologicalSpace Output) ↔
      ∀ (catalog : Unit → Input → Output) (candidate : Input → Output),
        CatalogEscape catalog candidate →
          CatalogEscape (observedCatalog observe catalog)
            (observedCandidate observe candidate) := by
  apply Iff.trans
    (partitionTopology_eq_discrete_iff_injective
      (show Concept Output Observation from observe))
  exact injective_iff_preserves_unit_catalog_escape observe

#print axioms partitionTopology_eq_discrete_iff_injective
#print axioms discrete_partition_iff_preserves_unit_catalog_escape

end D5.S3.ConceptDynamics.ObservationTopology.FaithfulObservationTopology
