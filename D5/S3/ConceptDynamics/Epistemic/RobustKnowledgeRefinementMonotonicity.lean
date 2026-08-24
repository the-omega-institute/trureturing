/- GID: D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeRefinementMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/RobustKnowledgeRefinementMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Robust knowledge is monotone under evidence refinement. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/- Library-search audit trail (2026-08-25):
   * Exact family hits `Refines` in `ConceptJoinUniversal` and `robustKnowledge`
     in `RobustKnowledgeConjunction` are the source factorization order and the
     source admissible-fiber knowledge predicate; both are imported and reused.
   * Searches for `robustKnowledge.*Refines`, `Refines.*robustKnowledge`, and
     `robust_knowledge.*refin` under `D5` found no theorem combining them.
   * Pinned Mathlib contains `Function.FactorsThrough` and composition lemmas,
     but no packaged admissible anchored knowledge-monotonicity theorem. The
     established family relation is used directly instead. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeRefinementMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/-- Knowledge on an admissible coarse-evidence fiber remains true on every
refined-evidence fiber contained in it. -/
theorem robust_knowledge_monotone_under_refinement
    {X B B' : Type*} (admissible : X -> Prop)
    (coarseEvidence : Concept X B) (refinedEvidence : Concept X B')
    (predicate : X -> Prop) (anchor : X)
    (refinement : Refines coarseEvidence refinedEvidence)
    (knowledge : robustKnowledge admissible coarseEvidence predicate anchor) :
    robustKnowledge admissible refinedEvidence predicate anchor := by
  rcases refinement with ⟨factor, factorization⟩
  rcases knowledge with ⟨anchorAdmissible, anchorTruth, coarseFiberTruth⟩
  refine ⟨anchorAdmissible, anchorTruth, ?_⟩
  intro state stateInRefinedFiber
  apply coarseFiberTruth state
  refine ⟨stateInRefinedFiber.1, ?_⟩
  rw [factorization]
  change factor (refinedEvidence state) = factor (refinedEvidence anchor)
  exact congrArg factor stateInRefinedFiber.2

#print axioms robust_knowledge_monotone_under_refinement

end D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeRefinementMonotonicity
