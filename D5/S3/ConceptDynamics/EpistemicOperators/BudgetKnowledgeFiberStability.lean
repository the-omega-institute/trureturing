/- GID: D5/S3/ConceptDynamics/EpistemicOperators/BudgetKnowledgeFiberStability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EpistemicOperators/BudgetKnowledgeFiberStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Budget knowledge is exactly constancy on every joint-readout fiber. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/- Library-search audit trail (2026-08-27):
   * The repository exact hit `answerability_criterion` has the requested
     factorization/fiber-constancy iff as its first public conjunct; it is
     imported and applied directly below.
   * The existing `robustKnowledge` and `fiberKnowledge` primitives concern an
     admissible anchor fiber and a state-indexed modal operator, respectively;
     neither is the source's global factorization predicate.
   * Pinned Mathlib's exact theorem `Function.factorsThrough_iff` underlies the
     imported repository theorem. Loogle and LeanSearch returned that same
     declaration; no local factorization proof is repeated here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EpistemicOperators.BudgetKnowledgeFiberStability

open D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/-- Budget knowledge is the source definition: the predicate factors through
the joint readout. -/
def budgetKnowledge {X O B : Type*} (readout : X -> O) (predicate : X -> B) : Prop :=
  exists observable : O -> B, predicate = observable ∘ readout

/-- A predicate is budget-known exactly when it is constant on every joint-readout fiber. -/
theorem budget_knowledge_fiber_stability
    {X O B : Type*} (anchor : X) (readout : X -> O) (predicate : X -> B) :
    budgetKnowledge readout predicate <->
      forall x y, readout x = readout y -> predicate x = predicate y := by
  simpa only [budgetKnowledge] using
    (answerability_criterion anchor readout predicate).1

/-- Reverse probe: the public knowledge proposition forces equality of predicate
values on an identified pair. -/
example {X O B : Type*} (anchor : X) (readout : X -> O) (predicate : X -> B)
    (knowledge : budgetKnowledge readout predicate) {x y : X}
    (sameReadout : readout x = readout y) :
    predicate x = predicate y :=
  (budget_knowledge_fiber_stability anchor readout predicate).mp
    knowledge x y sameReadout

/-- Trivialization probe: a constant readout cannot know the nonconstant Boolean identity. -/
example :
    Not (budgetKnowledge (fun _ : Bool => ()) (id : Bool -> Bool)) := by
  intro knowledge
  have false_eq_true : (id : Bool -> Bool) false = id true :=
    (budget_knowledge_fiber_stability false (fun _ : Bool => ()) id).mp
      knowledge false true rfl
  exact Bool.false_ne_true false_eq_true

#print axioms budget_knowledge_fiber_stability

end D5.S3.ConceptDynamics.EpistemicOperators.BudgetKnowledgeFiberStability
