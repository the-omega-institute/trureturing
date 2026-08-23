/- GID: D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/VacuousOmniscience
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Empty evidence fibers validate every predicate, while witnesses prevent this collapse. -/

import D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'empty_fiber_knows_everything' D5 Golden/Frozen/accepted` returned no
     matches.
   * The requested structural search for `vacuous`, `Set.Nonempty`, nonempty fibers, and
     `absurd` found only unrelated finite-set, decomposition, and answer-coverage results.
   * Repository searches for `robustKnowledge` found `RobustKnowledgeConjunction` and
     `RobustKnowledgeFactivity`; the former supplies the definition reused below, while
     the latter proves the complementary anchored factivity result rather than this claim.
   * The pinned-Mathlib `smart_search.sh` query for empty evidence fibers and vacuous
     universal predicates returned no declarations. The proofs use only contradiction,
     a constantly false predicate, and the anchor conjunct of `robustKnowledge`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.VacuousOmniscience

open D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeConjunction

/-- Fiberwise knowledge at `b` says that the predicate holds at every admissible state
whose evidence is `b`; no actual state in the fiber is included in this condition. -/
def fiberKnowledge {X B : Type _}
    (admissible : X -> Prop) (evidence : X -> B) (b : B) (predicate : X -> Prop) : Prop :=
  forall x, admissible x -> evidence x = b -> predicate x

/-- An empty admissible evidence fiber makes every predicate fiberwise known. -/
theorem empty_fiber_knows_everything
    {X B : Type _} (admissible : X -> Prop) (evidence : X -> B) (b : B)
    (emptyFiber : forall x, admissible x -> Not (evidence x = b)) :
    forall predicate : X -> Prop, fiberKnowledge admissible evidence b predicate := by
  intro predicate x hAdmissible hEvidence
  exact (emptyFiber x hAdmissible hEvidence).elim

/-- A witness in the admissible evidence fiber supplies a predicate that is not known there. -/
theorem nonempty_fiber_excludes_vacuous_omniscience
    {X B : Type _} (admissible : X -> Prop) (evidence : X -> B) (b : B)
    (nonemptyFiber : exists x, admissible x /\ evidence x = b) :
    exists predicate : X -> Prop, Not (fiberKnowledge admissible evidence b predicate) := by
  rcases nonemptyFiber with ⟨x, hAdmissible, hEvidence⟩
  refine ⟨fun _ => False, ?_⟩
  intro hKnowledge
  exact hKnowledge x hAdmissible hEvidence

/-- The actual anchor carried by robust knowledge witnesses a nonempty evidence fiber. -/
theorem robust_knowledge_supplies_fiber_witness
    {X B : Type _} (admissible : X -> Prop) (evidence : X -> B)
    (predicate : X -> Prop) (anchor : X)
    (hKnowledge : robustKnowledge admissible evidence predicate anchor) :
    exists x, admissible x /\ evidence x = evidence anchor := by
  exact ⟨anchor, hKnowledge.1, rfl⟩

example :
    forall predicate : Unit -> Prop,
      fiberKnowledge (fun _ => True) (fun _ => false) true predicate := by
  apply empty_fiber_knows_everything
  intro x hAdmissible hEvidence
  exact Bool.false_ne_true hEvidence

#print axioms empty_fiber_knows_everything

end D5.S3.ConceptDynamics.Epistemic.VacuousOmniscience
