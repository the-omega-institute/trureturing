/- GID: D5/S3/ConceptDynamics/EpistemicRefinement/KnowledgeRefinementMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EpistemicRefinement/KnowledgeRefinementMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Knowledge by factorization is monotone under indexed readout refinement. -/

import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.RefinementFactorization.IndexedReadoutMonotonicity

/- Library-search audit trail (2026-08-26):
   * Exact D5 primitive hits `Refines` and `jointReadout` encode the source's
     factorization definition of budget knowledge; both are imported.
   * Exact D5 theorem hits `indexed_readout_monotonicity` and
     `refinement_transitive` supply the positive implication directly.
   * The set-valued `knowledge_monotone_under_nonempty_refinement` theorem uses
     a different carrier and is not an exact bind for indexed readouts.
   * Repository and pinned-Mathlib searches found no theorem that also exposes
     the source's converse countermodel. `Finset.notMem_empty` is the exact
     library hit used to prove the empty-budget readout is state-blind.
   * No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EpistemicRefinement.KnowledgeRefinementMonotonicity

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.RefinementFactorization.IndexedReadoutMonotonicity

universe u v w z

/-- A target that factors through a coarse indexed joint readout also factors
through every finer budget. The reverse implication is not general: one shared
Boolean readout and target admit nested budgets for which only the fine budget
knows the target. -/
theorem knowledge_monotone_under_indexed_refinement_with_converse_countermodel :
    (∀ {I : Type u} {X : Type v} {O : I → Type w} {Target : Type z}
        (q : ∀ i, X → O i) (target : X → Target)
        {J K : Finset I}, J ⊆ K →
        Refines target (jointReadout (fun j : J => q j.1)) →
        Refines target (jointReadout (fun k : K => q k.1))) ∧
      ∃ (q : ∀ _ : Unit, Bool → Bool) (target : Bool → Bool)
          (J K : Finset Unit),
        J ⊆ K ∧
          Refines target (jointReadout (fun k : K => q k.1)) ∧
          ¬Refines target (jointReadout (fun j : J => q j.1)) := by
  constructor
  · intro I X O Target q target J K hJK coarseKnowledge
    exact refinement_transitive target
      (jointReadout (fun j : J => q j.1))
      (jointReadout (fun k : K => q k.1))
      (indexed_readout_monotonicity q hJK).1 coarseKnowledge
  · let q : ∀ _ : Unit, Bool → Bool := fun _ => id
    let target : Bool → Bool := id
    refine ⟨q, target, (∅ : Finset Unit), {()}, ?_, ?_, ?_⟩
    · simp
    · refine ⟨fun values => values ⟨(), by simp⟩, ?_⟩
      funext state
      rfl
    · rintro ⟨factor, factorization⟩
      have sameCoarse :
          jointReadout (fun j : (∅ : Finset Unit) => q j.1) false =
            jointReadout (fun j : (∅ : Finset Unit) => q j.1) true := by
        funext j
        exact (Finset.notMem_empty j.1 j.2).elim
      have atFalse := congrFun factorization false
      have atTrue := congrFun factorization true
      have false_eq_true : false = true := by
        calc
          false = factor
              (jointReadout (fun j : (∅ : Finset Unit) => q j.1) false) := by
            simpa [target] using atFalse
          _ = factor
              (jointReadout (fun j : (∅ : Finset Unit) => q j.1) true) :=
            congrArg factor sameCoarse
          _ = true := by simpa [target] using atTrue.symm
      exact Bool.false_ne_true false_eq_true

#print axioms knowledge_monotone_under_indexed_refinement_with_converse_countermodel

end D5.S3.ConceptDynamics.EpistemicRefinement.KnowledgeRefinementMonotonicity
