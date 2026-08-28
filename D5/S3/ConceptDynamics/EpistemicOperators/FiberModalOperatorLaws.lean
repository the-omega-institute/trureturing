/- GID: D5/S3/ConceptDynamics/EpistemicOperators/FiberModalOperatorLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EpistemicOperators/FiberModalOperatorLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fiber knowledge is an interior operator and fiber possibility its dual closure. -/

import D5.S3.ConceptDynamics.Epistemic.FiberInteriorEquivalence
import D5.S3.ConceptDynamics.Epistemic.TopologicalKnowledgeOperator

/- Library-search audit trail (2026-08-26):
   * The exact family primitives `fiberKnowledge` and `partitionTopology`, and
     the exact bridge `fiber_interior_equivalence`, are imported and reused.
   * `topological_knowledge_operator_laws` already packages Mathlib's exact
     `interior_subset`, `interior_mono`, `interior_interior`, and
     `interior_inter` hits; the first four clauses below apply that package.
   * D5 body-shape searches for the existential same-readout possibility
     operator found no existing primitive or theorem, so it remains a public
     local construction rather than a competing top-level definition.
   * Pinned Mathlib's `ClosureOperator` has the requested three law fields, but
     no existing operator specializes them to this readout-fiber construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EpistemicOperators.FiberModalOperatorLaws

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Epistemic.FiberInteriorEquivalence
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.Epistemic.TopologicalKnowledgeOperator

/-- Knowledge along a concept readout is factive, monotone, idempotent, and
conjunction-preserving. Existential possibility along the same fiber is
extensive, monotone, idempotent, and classically dual to that knowledge. -/
theorem fiber_knowledge_and_possibility_operator_laws
    {X B : Type*} (readout : Concept X B) :
    (forall P : Set X, fiberKnowledge readout P ⊆ P) ∧
      (forall {P Q : Set X}, P ⊆ Q ->
        fiberKnowledge readout P ⊆ fiberKnowledge readout Q) ∧
      (forall P : Set X,
        fiberKnowledge readout (fiberKnowledge readout P) =
          fiberKnowledge readout P) ∧
      (forall P Q : Set X,
        fiberKnowledge readout (P ∩ Q) =
          fiberKnowledge readout P ∩ fiberKnowledge readout Q) ∧
      (let possibility : Set X -> Set X := fun P =>
          {a | ∃ x, readout x = readout a ∧ x ∈ P};
        (forall P : Set X, P ⊆ possibility P) ∧
          (forall {P Q : Set X}, P ⊆ Q -> possibility P ⊆ possibility Q) ∧
          (forall P : Set X, possibility (possibility P) = possibility P) ∧
          (forall P : Set X,
            fiberKnowledge readout P = (possibility (Pᶜ))ᶜ)) := by
  classical
  letI : TopologicalSpace X := partitionTopology readout
  have knowledge_eq_interior (P : Set X) :
      fiberKnowledge readout P = @interior X (partitionTopology readout) P := by
    ext x
    exact (fiber_interior_equivalence readout P x).symm
  have interior_laws := topological_knowledge_operator_laws (X := X)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P
    rw [knowledge_eq_interior P]
    exact interior_laws.1 P
  · intro P Q hPQ
    rw [knowledge_eq_interior P, knowledge_eq_interior Q]
    exact interior_laws.2.1 hPQ
  · intro P
    calc
      fiberKnowledge readout (fiberKnowledge readout P) =
          interior (fiberKnowledge readout P) := knowledge_eq_interior _
      _ = interior (interior P) := congrArg interior (knowledge_eq_interior P)
      _ = interior P := interior_laws.2.2.2 P
      _ = fiberKnowledge readout P := (knowledge_eq_interior P).symm
  · intro P Q
    rw [knowledge_eq_interior (P ∩ Q), interior_laws.2.2.1 P Q,
      ← knowledge_eq_interior P, ← knowledge_eq_interior Q]
  · dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro P a ha
      exact ⟨a, rfl, ha⟩
    · intro P Q hPQ a
      rintro ⟨x, hxa, hxP⟩
      exact ⟨x, hxa, hPQ hxP⟩
    · intro P
      ext a
      constructor
      · rintro ⟨x, hxa, y, hyx, hyP⟩
        exact ⟨y, hyx.trans hxa, hyP⟩
      · rintro ⟨x, hxa, hxP⟩
        exact ⟨x, hxa, x, rfl, hxP⟩
    · intro P
      ext a
      constructor
      · intro hKnowledge hPossibility
        rcases hPossibility with ⟨x, hxa, hxNotP⟩
        exact hxNotP (hKnowledge x hxa)
      · intro hNotPossible x hxa
        by_contra hxNotP
        exact hNotPossible ⟨x, hxa, hxNotP⟩

#print axioms fiber_knowledge_and_possibility_operator_laws

end D5.S3.ConceptDynamics.EpistemicOperators.FiberModalOperatorLaws
