/- GID: D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Knowledge stable on every admissible state in an evidence fiber is closed under conjunction. -/

/- Library-search audit trail (2026-08-22):
   * The source definition of robust knowledge is at FORMAL_CONCEPT_DYNAMICS.md:1372-1387.
   * Repository searches for Know_E, robust knowledge, evidence fibers, and knowledge
     conjunction found no accepted declaration with this source predicate.
   * The direct logical construction below uses only conjunction introduction and
     universal instantiation; no stronger Mathlib theorem matched the source clause.
   * `loogle` and `leansearch` were unavailable on PATH during the search.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/-- A proposition is robustly known when it holds at the admissible anchor and
at every admissible state with the same evidence. -/
def robustKnowledge {X B : Type _}
    (admissible : X -> Prop) (evidence : X -> B)
    (predicate : X -> Prop) (anchor : X) : Prop :=
  And (admissible anchor) (And (predicate anchor)
    (forall x, And (admissible x) (evidence x = evidence anchor) -> predicate x))

/-- Robust knowledge on one evidence fiber is closed under conjunction. -/
theorem robust_knowledge_conjunction
    {X B : Type _} (admissible : X -> Prop) (evidence : X -> B)
    (P Q : X -> Prop) (anchor : X)
    (hP : robustKnowledge admissible evidence P anchor)
    (hQ : robustKnowledge admissible evidence Q anchor) :
    robustKnowledge admissible evidence (fun x => And (P x) (Q x)) anchor := by
  rcases hP with ⟨hAnchor, hPAnchor, hPFiber⟩
  rcases hQ with ⟨_, hQAnchor, hQFiber⟩
  refine ⟨hAnchor, ⟨hPAnchor, hQAnchor⟩, ?_⟩
  intro x hx
  exact ⟨hPFiber x hx, hQFiber x hx⟩

/-- The source premises are simultaneously satisfiable on a one-point
evidence space. -/
example :
    robustKnowledge (fun _ : Bool => True) (fun _ : Bool => ())
      (fun _ : Bool => True) true := by
  refine ⟨by trivial, by trivial, ?_⟩
  intro x hx
  trivial

#print axioms robust_knowledge_conjunction

end D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction
