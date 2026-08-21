/- GID: D5/S3/ConceptDynamics/Epistemic/PartitionAndGeneralNegativeIntrospectionContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/PartitionAndGeneralNegativeIntrospectionContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Contrast partition knowledge with general negative-introspection failure. -/

import D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.PartitionAndGeneralNegativeIntrospectionContrast

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection

/- Library-search audit trail (2026-08-22):
   * The frozen family theorem `partition_knowledge_negative_introspection` is an
     exact hit for the partition-topology conjunct and is applied directly.
   * Repository searches found no existing declaration for the contrast conjunct.
   * Pinned Mathlib's `Topology.Order` supplies the Sierpinski topology on `Prop`
     together with `isOpen_singleton_true` and `nhds_false`; the latter identifies
     the neighborhood filter used to refute negative introspection at `False`. -/

/--
Readout-partition knowledge satisfies negative introspection, while general
topological knowledge, defined by interior, need not: in the Sierpinski topology
on `Prop`, the predicate `{True}` fails negative introspection at `False`.
-/
theorem partition_and_general_negative_introspection_contrast :
    (∀ {X B : Type _} (readout : Concept X B) (predicate : Set X),
      @IsOpen X (partitionTopology readout)
          ((fiberKnowledge readout predicate)ᶜ) ∧
      ∀ x, x ∉ fiberKnowledge readout predicate →
        x ∈ fiberKnowledge readout
          ((fiberKnowledge readout predicate)ᶜ)) ∧
    ¬ (∀ x : Prop,
      x ∉ interior ({True} : Set Prop) →
      x ∈ interior ((interior ({True} : Set Prop))ᶜ)) := by
  constructor
  · intro X B readout predicate
    exact partition_knowledge_negative_introspection readout predicate
  · intro h
    have hFalse := h False
    rw [interior_eq_iff_isOpen.mpr isOpen_singleton_true] at hFalse
    have hFailure : False ∈ interior (({True} : Set Prop)ᶜ) := hFalse (by simp)
    rw [mem_interior_iff_mem_nhds, nhds_false] at hFailure
    have hTrue : True ∈ (({True} : Set Prop)ᶜ) := hFailure True
    exact hTrue (by simp)

#print axioms partition_and_general_negative_introspection_contrast

end D5.S3.ConceptDynamics.Epistemic.PartitionAndGeneralNegativeIntrospectionContrast
