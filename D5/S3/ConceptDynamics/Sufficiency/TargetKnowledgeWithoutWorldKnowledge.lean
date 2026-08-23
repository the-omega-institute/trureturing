/- GID: D5/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/TargetKnowledgeWithoutWorldKnowledge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target sufficiency can retain less information than the complete world readout. -/

import D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'target_knowledge_without_world_knowledge' D5
     Golden/Frozen/accepted` returned no hit.
   * `rg -n 'top_X|topConcept|world|complete.*information'
     D5/S3/ConceptDynamics/ --glob '*.lean'` found uses of "world" but no
     complete-world concept or theorem duplicating this counterexample.
   * The requested `Disclosure/ExactTargetForcedLeak.lean` path is absent in
     this worktree. Repository search found `ConceptEquivalent` in
     `Interventions.RedundantAppealDefectPersistence`, which is imported directly.
   * `UniversalSufficiencyFactorization.universal_sufficiency_factorization`
     is the exact existing fiber-constancy characterization of target sufficiency;
     it is reused below. Only Boolean pair separation is proved locally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.TargetKnowledgeWithoutWorldKnowledge

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- The target answer observes only the first coordinate of a two-bit world. -/
def targetReadout : Bool × Bool → Bool :=
  Prod.fst

/-- The answer-sufficient concept retains exactly the target coordinate. -/
def answerConcept : Concept (Bool × Bool) Bool :=
  Prod.fst

/-- Complete world knowledge is modeled by the identity readout. -/
def completeWorldReadout : Concept (Bool × Bool) (Bool × Bool) :=
  id

/-- The first-coordinate concept answers the target while failing to recover the
second world coordinate. -/
theorem answer_concept_sufficient_but_incomplete :
    Refines (canonicalTargetReadout targetReadout) answerConcept ∧
      ¬ConceptEquivalent answerConcept completeWorldReadout := by
  constructor
  · have fiberConstant : ∀ ⦃x y : Bool × Bool⦄,
        answerConcept x = answerConcept y → targetReadout x = targetReadout y := by
      intro x y hxy
      exact hxy
    have characterization :=
      universal_sufficiency_factorization answerConcept targetReadout
    exact characterization.1.mpr (characterization.2.mpr fiberConstant)
  · intro equivalent
    rcases equivalent.2 with ⟨factor, hfactor⟩
    have hfalse := congrFun hfactor (false, false)
    have htrue := congrFun hfactor (false, true)
    change (false, false) = factor false at hfalse
    change (false, true) = factor false at htrue
    have hpairs : (false, false) = (false, true) := hfalse.trans htrue.symm
    exact Bool.false_ne_true (congrArg Prod.snd hpairs)

/-- Some target is recoverable from a concept that is not equivalent to the
complete-world identity readout. -/
theorem target_knowledge_without_world_knowledge :
    ∃ (X Target Coordinate : Type) (T : X → Target) (C : Concept X Coordinate),
      Refines (canonicalTargetReadout T) C ∧
        ¬ConceptEquivalent C (id : Concept X X) := by
  refine ⟨Bool × Bool, Bool, Bool, targetReadout, answerConcept, ?_⟩
  simpa [completeWorldReadout] using answer_concept_sufficient_but_incomplete

example :
    Refines (canonicalTargetReadout targetReadout) answerConcept ∧
      ¬ConceptEquivalent answerConcept completeWorldReadout := by
  exact answer_concept_sufficient_but_incomplete

#print axioms target_knowledge_without_world_knowledge

end D5.S3.ConceptDynamics.Sufficiency.TargetKnowledgeWithoutWorldKnowledge
