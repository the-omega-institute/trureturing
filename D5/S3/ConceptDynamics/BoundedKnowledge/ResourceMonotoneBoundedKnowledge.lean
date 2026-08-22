/- GID: D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform bounded knowledge is monotone in resources and refines structural knowledge. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'resource_monotone_bounded_knowledge' D5 Golden/Frozen/accepted`
     returned no matches.
   * `rg -n 'Know|bounded_knowledge|resource_monoton' D5/ --glob '*.lean'`
     found unrelated knowledge declarations, including `robustKnowledge`, `Knows`, and
     `KnowledgeSpace`, but no resource-indexed family of decision programs.
   * A pinned-Mathlib search found `Monotone` and `Set.mem_of_subset_of_mem`; the main
     proof uses monotonicity directly. No declaration packages the structural consequence
     or the missing-program counterexample, so those use only propositional reasoning,
     equality substitution, existential elimination, and empty-set membership.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.BoundedKnowledge.ResourceMonotoneBoundedKnowledge

/-- Bounded knowledge combines truth at an admissible anchor with a uniform classifier
available within the given resource budget. -/
def boundedKnowledge {X B R : Type*}
    (programs : R -> Set (B -> Prop)) (admissible : X -> Prop)
    (evidence : X -> B) (predicate : X -> Prop) (anchor : X) (budget : R) : Prop :=
  admissible anchor ∧ predicate anchor ∧
    ∃ classifier, classifier ∈ programs budget ∧
      ∀ x, predicate x ↔ classifier (evidence x)

/-- Structural knowledge requires truth at an admissible anchor and constancy of the
predicate on every fiber of the evidence readout. -/
def structuralKnowledge {X B : Type*}
    (admissible : X -> Prop) (evidence : X -> B)
    (predicate : X -> Prop) (anchor : X) : Prop :=
  admissible anchor ∧ predicate anchor ∧
    ∀ x y, evidence x = evidence y -> (predicate x ↔ predicate y)

/-- A monotone program family turns an increase in budget into an increase in bounded
knowledge; monotonicity makes the order hypothesis mathematically load-bearing. -/
theorem resource_monotone_bounded_knowledge
    {X B R : Type*} [Preorder R]
    (programs : R -> Set (B -> Prop)) (hprograms : Monotone programs)
    (admissible : X -> Prop) (evidence : X -> B)
    (predicate : X -> Prop) (anchor : X) {r s : R} (hrs : r ≤ s) :
    boundedKnowledge programs admissible evidence predicate anchor r ->
      boundedKnowledge programs admissible evidence predicate anchor s := by
  rintro ⟨hAdmissible, hTrue, classifier, hAvailable, hUniform⟩
  exact ⟨hAdmissible, hTrue, classifier, hprograms hrs hAvailable, hUniform⟩

/-- Every uniform bounded classifier makes the predicate constant on evidence fibers. -/
theorem bounded_knowledge_implies_structural_knowledge
    {X B R : Type*} (programs : R -> Set (B -> Prop))
    (admissible : X -> Prop) (evidence : X -> B)
    (predicate : X -> Prop) (anchor : X) (budget : R) :
    boundedKnowledge programs admissible evidence predicate anchor budget ->
      structuralKnowledge admissible evidence predicate anchor := by
  rintro ⟨hAdmissible, hTrue, classifier, _, hUniform⟩
  refine ⟨hAdmissible, hTrue, ?_⟩
  intro x y hEvidence
  rw [hUniform x, hUniform y, hEvidence]

/-- Structural knowledge need not be bounded knowledge: the predicate is constant on the
one evidence fiber, but the empty program family contains no classifier at budget zero. -/
theorem structural_knowledge_not_bounded_counterexample :
    structuralKnowledge
        (fun _ : Bool => True) (fun _ : Bool => ())
        (fun _ : Bool => True) true ∧
      ¬boundedKnowledge (fun _ : Nat => (∅ : Set (Unit -> Prop)))
        (fun _ : Bool => True) (fun _ : Bool => ())
        (fun _ : Bool => True) true 0 := by
  constructor
  · refine ⟨by trivial, by trivial, ?_⟩
    intro x y hEvidence
    exact Iff.rfl
  · rintro ⟨_, _, classifier, hAvailable, _⟩
    exact hAvailable

example :
    structuralKnowledge
        (fun _ : Bool => True) (fun _ : Bool => ())
        (fun _ : Bool => True) true ∧
      ¬boundedKnowledge (fun _ : Nat => (∅ : Set (Unit -> Prop)))
        (fun _ : Bool => True) (fun _ : Bool => ())
        (fun _ : Bool => True) true 0 :=
  structural_knowledge_not_bounded_counterexample

#print axioms resource_monotone_bounded_knowledge

end D5.S3.ConceptDynamics.BoundedKnowledge.ResourceMonotoneBoundedKnowledge
