/- GID: D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Show that fiberwise knowledge has open failure and negative introspection. -/

/- Library-search audit trail (2026-08-22):
   * The source defines knowledge by universal truth on the current readout fiber.
   * Repository searches for partition knowledge and negative introspection found no
     accepted declaration proving the source's two-clause theorem.
   * Pinned Mathlib provides `isOpen_induced_iff`, `isOpen_discrete`, and
     `Set.preimage_compl`; no exact theorem packages both source clauses.
-/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Topology.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The states whose entire current readout fiber satisfies a predicate. -/
def fiberKnowledge {X B : Type _}
    (readout : Concept X B) (predicate : Set X) : Set X :=
  {x | ∀ y, readout y = readout x → y ∈ predicate}

/-- The partition topology induced by a readout into a discrete coordinate space. -/
@[reducible] def partitionTopology {X B : Type _}
    (readout : Concept X B) : TopologicalSpace X :=
  TopologicalSpace.induced readout ⊥

/--
The failure set of fiberwise knowledge is open in the readout partition topology,
and failure at a state is itself known throughout that state's readout fiber.
-/
theorem partition_knowledge_negative_introspection
    {X B : Type _} (readout : Concept X B) (predicate : Set X) :
    @IsOpen X (partitionTopology readout) ((fiberKnowledge readout predicate)ᶜ) ∧
    ∀ x, x ∉ fiberKnowledge readout predicate →
      x ∈ fiberKnowledge readout ((fiberKnowledge readout predicate)ᶜ) := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  constructor
  · change @IsOpen X (TopologicalSpace.induced readout (⊥ : TopologicalSpace B))
      ((fiberKnowledge readout predicate)ᶜ)
    apply isOpen_induced_iff.mpr
    refine ⟨{b | ∃ y, readout y = b ∧ y ∉ predicate}, isOpen_discrete _, ?_⟩
    ext x
    simp only [fiberKnowledge, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_preimage]
    push Not
    rfl
  · intro x hx
    change ∀ z, readout z = readout x → z ∈ (fiberKnowledge readout predicate)ᶜ
    intro z hz
    change z ∉ fiberKnowledge readout predicate
    intro hzKnowledge
    apply hx
    intro y hy
    exact hzKnowledge y (hy.trans hz.symm)

example (predicate : Set Bool) :
    @IsOpen Bool (partitionTopology (fun x : Bool => x))
        ((fiberKnowledge (fun x : Bool => x) predicate)ᶜ) ∧
      ∀ x, x ∉ fiberKnowledge (fun x : Bool => x) predicate →
        x ∈ fiberKnowledge (fun x : Bool => x)
          ((fiberKnowledge (fun x : Bool => x) predicate)ᶜ) :=
  partition_knowledge_negative_introspection (fun x : Bool => x) predicate

#print axioms partition_knowledge_negative_introspection

end D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
