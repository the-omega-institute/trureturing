/- GID: D5/S0/Rewriting/Quotients/AnswerabilityCriterion
   generality: G
   mirror-B: D5/B/S0/Rewriting/Quotients/AnswerabilityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Answerability is equivalent to fiber constancy and an empty defect relation. -/

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-20):
   * Exact pinned-Mathlib hit: `Function.factorsThrough_iff` characterizes
     fiber constancy by factorization through a function when the target is
     nonempty; it is applied directly below.
   * Exact pinned-Mathlib hit: `Function.FactorsThrough` is the source's
     fiber-constancy clause; it is unfolded only to expose that public clause.
   * Repository hit `relative_identity_refinement` proves the forward kernel
     inclusion induced by a supplied factor map, but not the converse or the
     three-way criterion.
   * Repository searches for answerability, fiber constancy, factorization,
     and empty kernel difference found no declaration packaging all clauses. -/

namespace D5.S0.Rewriting.Quotients.AnswerabilityCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For an anchored state space, a question factors through a concept exactly
when it is constant on every concept fiber, equivalently when no pair has the
same concept value and distinct question values. -/
theorem answerability_criterion
    {X ConceptAnswer QuestionAnswer : Type*} (anchor : X)
    (concept : X → ConceptAnswer) (question : X → QuestionAnswer) :
    ((∃ answer : ConceptAnswer → QuestionAnswer, question = answer ∘ concept) ↔
      ∀ ⦃x y : X⦄, concept x = concept y → question x = question y) ∧
      ((∀ ⦃x y : X⦄, concept x = concept y → question x = question y) ↔
        {pair : X × X |
            concept pair.1 = concept pair.2 ∧ question pair.1 ≠ question pair.2} = ∅) ∧
      ({pair : X × X |
          concept pair.1 = concept pair.2 ∧ question pair.1 ≠ question pair.2} = ∅ ↔
        ∃ answer : ConceptAnswer → QuestionAnswer, question = answer ∘ concept) := by
  letI : Nonempty QuestionAnswer := ⟨question anchor⟩
  have hfactor :
      (∃ answer : ConceptAnswer → QuestionAnswer, question = answer ∘ concept) ↔
        ∀ ⦃x y : X⦄, concept x = concept y → question x = question y := by
    simpa only [Function.FactorsThrough] using
      (Function.factorsThrough_iff (f := concept) question).symm
  have hdefect :
      (∀ ⦃x y : X⦄, concept x = concept y → question x = question y) ↔
        {pair : X × X |
            concept pair.1 = concept pair.2 ∧ question pair.1 ≠ question pair.2} = ∅ := by
    constructor
    · intro hfiber
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨x, y⟩ ⟨hsame, hdifferent⟩
      exact hdifferent (hfiber hsame)
    · intro hempty x y hsame
      by_contra hdifferent
      have hmember :
          (x, y) ∈ {pair : X × X |
            concept pair.1 = concept pair.2 ∧ question pair.1 ≠ question pair.2} :=
        ⟨hsame, hdifferent⟩
      rw [hempty] at hmember
      exact hmember
  exact ⟨hfactor, hdefect, hdefect.symm.trans hfactor.symm⟩

/-- The public state-domain premise is inhabited. -/
example : PUnit := PUnit.unit

/-- Constant Boolean readouts witness simultaneous satisfiability of the
public data and the factorization clause. -/
example :
    ∃ (_anchor : PUnit) (concept : PUnit → Bool) (question : PUnit → Bool),
      ∃ answer : Bool → Bool, question = answer ∘ concept := by
  exact ⟨PUnit.unit, fun _ => false, fun _ => true, fun _ => true, rfl⟩

#print axioms answerability_criterion

end D5.S0.Rewriting.Quotients.AnswerabilityCriterion
