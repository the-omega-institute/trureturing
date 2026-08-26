/- GID: D5/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Readout refinement along dependency paths enlarges answerability and shrinks target defects. -/

import D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import Mathlib.Logic.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.KnowledgeAlongDependency

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Every dependency edge carries a factorization from the dependent readout to its prerequisite readout. -/
def EdgeRefines
    {Node State : Type*} {Coordinate : Node → Type*}
    (edge : Node → Node → Prop)
    (readout : ∀ node, Concept State (Coordinate node)) : Prop :=
  ∀ ⦃prerequisite dependent : Node⦄,
    edge prerequisite dependent →
      Refines (readout prerequisite) (readout dependent)

/-- Refinement witnesses compose along reflexive-transitive dependency paths. -/
theorem refines_of_reachable
    {Node State : Type*} {Coordinate : Node → Type*}
    {edge : Node → Node → Prop}
    {readout : ∀ node, Concept State (Coordinate node)}
    (edgeRefines : EdgeRefines edge readout)
    {first last : Node}
    (path : Relation.ReflTransGen edge first last) :
    Refines (readout first) (readout last) := by
  induction path with
  | refl => exact ⟨id, rfl⟩
  | tail _ edgeStep inductionHypothesis =>
      exact refinement_transitive
        _ _ _
        (edgeRefines edgeStep) inductionHypothesis

/-- Every question answerable upstream remains answerable downstream. -/
theorem answerableQuestions_mono_of_reachable
    {Node State : Type*} {Coordinate : Node → Type*}
    {edge : Node → Node → Prop}
    {readout : ∀ node, Concept State (Coordinate node)}
    (edgeRefines : EdgeRefines edge readout)
    {first last : Node}
    (path : Relation.ReflTransGen edge first last) :
    AnswerableQuestions (readout first) ⊆ AnswerableQuestions (readout last) :=
  answerable_questions_mono
    (readout first) (readout last)
    (refines_of_reachable edgeRefines path)

/-- Target defects are antitone along a refinement-carrying dependency path. -/
theorem defectRelation_antitone_of_reachable
    {Node State Target : Type*} {Coordinate : Node → Type*}
    {edge : Node → Node → Prop}
    {readout : ∀ node, Concept State (Coordinate node)}
    (edgeRefines : EdgeRefines edge readout)
    {first last : Node}
    (path : Relation.ReflTransGen edge first last)
    (target : Concept State Target) :
    defectRelation (readout last) target ⊆
      defectRelation (readout first) target := by
  rcases refines_of_reachable edgeRefines path with ⟨factor, factors⟩
  rintro pair ⟨sameFine, targetDifferent⟩
  refine ⟨?_, targetDifferent⟩
  rw [factors]
  exact congrArg factor sameFine

/-- The set of risky targets can only shrink along a refinement-carrying path. -/
theorem targetRisk_antitone_of_reachable
    {Node State Target : Type*} {Coordinate : Node → Type*}
    {edge : Node → Node → Prop}
    {readout : ∀ node, Concept State (Coordinate node)}
    (edgeRefines : EdgeRefines edge readout)
    {first last : Node}
    (path : Relation.ReflTransGen edge first last)
    (targets : Set (Concept State Target)) :
    targetRisk (readout last) targets ⊆ targetRisk (readout first) targets := by
  exact (refinement_reduces_target_risk_and_raises_cost
    (readout first) (readout last) targets
    (refines_of_reachable edgeRefines path)).1

#print axioms refines_of_reachable
#print axioms answerableQuestions_mono_of_reachable
#print axioms defectRelation_antitone_of_reachable

end D5.S3.ConceptDynamics.DagSemantics.KnowledgeAlongDependency
