/- GID: D5/S3/ConceptDynamics/Epistemic/TopologicalKnowledgeOperator
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/TopologicalKnowledgeOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Topological interior satisfies the four knowledge-operator laws. -/

import Mathlib.Topology.Closure

/- Library-search audit trail (2026-08-23):
   * Exact pinned-Mathlib hits `interior_subset`, `interior_mono`,
     `interior_inter`, and `interior_interior` are all declared in
     `Mathlib.Topology.Closure` and respectively state the four source clauses.
   * Repository searches for a single accepted declaration packaging all four
     topological knowledge-operator laws found no exact hit.
   * `loogle` and `leansearch` were unavailable on PATH; the four exact local
     Mathlib hits were imported and applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.TopologicalKnowledgeOperator

/-- The canonical topological knowledge operator, given by interior, is
factive, monotone, finite-intersection preserving, and idempotent. -/
theorem topological_knowledge_operator_laws
    {X : Type*} [TopologicalSpace X] :
    (forall P : Set X, interior P ⊆ P) ∧
      (forall {P Q : Set X}, P ⊆ Q -> interior P ⊆ interior Q) ∧
      (forall P Q : Set X, interior (P ∩ Q) = interior P ∩ interior Q) ∧
      (forall P : Set X, interior (interior P) = interior P) := by
  exact ⟨fun _ => interior_subset, fun h => interior_mono h,
    fun _ _ => interior_inter, fun _ => interior_interior⟩

#print axioms topological_knowledge_operator_laws

end D5.S3.ConceptDynamics.Epistemic.TopologicalKnowledgeOperator
