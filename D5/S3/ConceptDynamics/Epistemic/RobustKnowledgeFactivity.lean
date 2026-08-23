/- GID: D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeFactivity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/RobustKnowledgeFactivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Robust knowledge entails truth at its admissible evidence anchor. -/

/- Library-search audit trail (2026-08-22):
   * The repository exact hit `robustKnowledge` constructs the source knowledge predicate
     from admissibility, an evidence channel, anchor truth, and fiberwise stability; it is
     imported and reused below.
   * Searches for an existing factivity theorem over that primitive returned no hit.
   * The proof directly applies the core conjunction projection to the imported definition;
     no stronger packaged theorem matches this repository-specific predicate. -/

import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity

open D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/-- Knowledge stable throughout an admissible evidence fiber is factual at its anchor. -/
theorem robust_knowledge_factivity
    {X B : Type _} (admissible : X -> Prop) (evidence : X -> B)
    (predicate : X -> Prop) (anchor : X)
    (hKnowledge : robustKnowledge admissible evidence predicate anchor) :
    predicate anchor :=
  hKnowledge.2.1

/- A one-point evidence channel supplies a concrete inhabited domain and a satisfiable
knowledge hypothesis. -/
example :
    let admissible : Bool -> Prop := fun _ => True
    let evidence : Bool -> Bool := fun x => x
    let predicate : Bool -> Prop := fun x => x = true
    robustKnowledge admissible evidence predicate true ∧ predicate true := by
  dsimp
  have hKnowledge :
      robustKnowledge (fun _ : Bool => True) (fun x : Bool => x)
        (fun x : Bool => x = true) true := by
    refine ⟨trivial, rfl, ?_⟩
    intro x hx
    simpa using hx.2
  exact ⟨hKnowledge, robust_knowledge_factivity
    (admissible := fun _ : Bool => True) (evidence := fun x : Bool => x)
    (predicate := fun x : Bool => x = true) (anchor := true) hKnowledge⟩

#print axioms robust_knowledge_factivity

end D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity
