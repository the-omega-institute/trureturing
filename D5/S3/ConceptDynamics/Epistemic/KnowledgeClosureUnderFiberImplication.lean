/- GID: D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Knowledge is closed under implications valid on its admissible evidence fiber. -/

import D5.S3.ConceptDynamics.BoundedKnowledge.ResourceMonotoneBoundedKnowledge
import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'knowledge_closure_under_fiber_implication' D5 Golden/Frozen/accepted`
     returned no matches.
   * `rg -n 'Know|knowledge|fiber.*implication|closure' D5/S3/ConceptDynamics/
     --glob '*.lean'` found `robustKnowledge` and `robust_knowledge_conjunction` in
     `RobustKnowledgeConjunction.lean`; the former exactly models truth throughout the
     admissible anchor fiber, and the latter already formalizes Theorem 20.3.
   * The same search found `structuralKnowledge` in
     `ResourceMonotoneBoundedKnowledge.lean`. It is stronger in a different direction:
     it requires global constancy on every evidence fiber, while `robustKnowledge` asks
     for truth only on the admissible anchor fiber. The relation proved below reuses both
     definitions.
   * The pinned-Mathlib `smart_search.sh 'fiber implication predicate closure'` search
     returned no declarations. No upstream result packages fiber-restricted implication,
     so the closure proof uses only universal instantiation and conjunction introduction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.KnowledgeClosureUnderFiberImplication

open D5.S3.ConceptDynamics.BoundedKnowledge.ResourceMonotoneBoundedKnowledge
open D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/-- An implication available to the observer is valid at every admissible state in the
anchor's evidence fiber; it need not hold elsewhere in the ambient state space. -/
def fiberImplication {X B : Type*}
    (admissible : X -> Prop) (evidence : X -> B)
    (P Q : X -> Prop) (anchor : X) : Prop :=
  forall x, admissible x -> evidence x = evidence anchor -> P x -> Q x

/-- Knowledge is closed under an implication valid inside the admissible evidence fiber. -/
theorem knowledge_closure_under_fiber_implication
    {X B : Type*} (admissible : X -> Prop) (evidence : X -> B)
    (P Q : X -> Prop) (anchor : X)
    (hP : robustKnowledge admissible evidence P anchor)
    (hPQ : fiberImplication admissible evidence P Q anchor) :
    robustKnowledge admissible evidence Q anchor := by
  rcases hP with ⟨hAnchor, hPAnchor, hPFiber⟩
  refine ⟨hAnchor, hPQ anchor hAnchor rfl hPAnchor, ?_⟩
  intro x hx
  exact hPQ x hx.1 hx.2 (hPFiber x hx)

/-- Global structural knowledge entails truth on the admissible anchor fiber. -/
theorem structural_knowledge_implies_robust_knowledge
    {X B : Type*} (admissible : X -> Prop) (evidence : X -> B)
    (P : X -> Prop) (anchor : X)
    (hP : structuralKnowledge admissible evidence P anchor) :
    robustKnowledge admissible evidence P anchor := by
  rcases hP with ⟨hAnchor, hPAnchor, hConstant⟩
  refine ⟨hAnchor, hPAnchor, ?_⟩
  intro x hx
  exact (hConstant x anchor hx.2).mpr hPAnchor

/-- Fiber validity is genuinely weaker than ambient implication: on this model the
implication fails at `false`, outside the sole admissible fiber, while knowledge closes. -/
theorem fiber_implication_not_global_counterexample :
    let admissible : Bool -> Prop := fun x => x = true
    let evidence : Bool -> Unit := fun _ => ()
    let P : Bool -> Prop := fun _ => True
    let Q : Bool -> Prop := fun x => x = true
    robustKnowledge admissible evidence P true ∧
      fiberImplication admissible evidence P Q true ∧
      (Not (forall x, P x -> Q x)) ∧
      robustKnowledge admissible evidence Q true := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, by trivial, ?_⟩
    intro x hx
    trivial
  · intro x hx _ _
    exact hx
  · intro hGlobal
    exact Bool.noConfusion (hGlobal false (by trivial))
  · refine ⟨rfl, rfl, ?_⟩
    intro x hx
    exact hx.1

example :
    robustKnowledge (fun x : Bool => x = true) (fun _ : Bool => ())
      (fun x => x = true) true := by
  apply knowledge_closure_under_fiber_implication
    (P := fun _ => True)
  · exact fiber_implication_not_global_counterexample.1
  · exact fiber_implication_not_global_counterexample.2.1

#print axioms knowledge_closure_under_fiber_implication

end D5.S3.ConceptDynamics.Epistemic.KnowledgeClosureUnderFiberImplication
