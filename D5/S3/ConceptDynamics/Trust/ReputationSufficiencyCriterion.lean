/- GID: D5/S3/ConceptDynamics/Trust/ReputationSufficiencyCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Trust/ReputationSufficiencyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reputation determines a target exactly by canonical target refinement. -/

import D5.S3.ConceptDynamics.Governance.JudgmentRelativeAnalogyCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * Exact family hits `Refines`, `TargetImage`, and `canonicalTargetReadout`
     provide the source refinement order and canonical target concept; all are
     imported through `JudgmentRelativeAnalogyCriterion` and reused directly.
   * The exact repository theorem `judgment_relative_analogy_criterion` states
     that a same-readout, different-target pair refutes target sufficiency. Its
     obstruction half is applied directly below.
   * Searches for reputation and trustworthiness under `ConceptDynamics` found
     no existing formal module. `inductive_sufficiency_criterion` is adjacent,
     but factors through the realized history image rather than the canonical
     target-image concept used by the source.
   * Pinned Mathlib hits `Function.FactorsThrough`, `Set.rangeFactorization`,
     and `Setoid.ker`; no upstream theorem combines all public clauses here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Trust.ReputationSufficiencyCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Governance.JudgmentRelativeAnalogyCriterion
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Reputation is constructed by scoring full history. It determines future
trustworthiness exactly when the canonical target concept factors through that
score. A score collision with different targets witnesses insufficiency and
different induced kernels. -/
theorem reputation_sufficiency_criterion
    {X History Score Trustworthiness : Type*}
    (history : Concept X History) (score : History -> Score)
    (trustworthiness : X -> Trustworthiness) :
    let reputation : Concept X Score := score ∘ history
    ((exists predictor : Score -> TargetImage trustworthiness,
        forall state,
          (predictor (reputation state)).1 = trustworthiness state) <->
      Refines (canonicalTargetReadout trustworthiness) reputation) /\
    ((exists x y,
        reputation x = reputation y /\
          trustworthiness x ≠ trustworthiness y) ->
      Not (Refines (canonicalTargetReadout trustworthiness) reputation) /\
        Setoid.ker reputation ≠ Setoid.ker trustworthiness) := by
  dsimp only
  constructor
  · constructor
    · rintro ⟨predictor, predicts⟩
      refine ⟨predictor, ?_⟩
      funext state
      apply Subtype.ext
      simp only [canonicalTargetReadout, Function.comp_apply]
      exact (predicts state).symm
    · rintro ⟨predictor, predicts⟩
      refine ⟨predictor, ?_⟩
      intro state
      have pointwise := congrFun predicts state
      have targetValues := congrArg Subtype.val pointwise
      simpa only [canonicalTargetReadout, Function.comp_apply] using targetValues.symm
  intro collision
  constructor
  · exact
      (judgment_relative_analogy_criterion
        (score ∘ history) trustworthiness).2 collision
  · rcases collision with ⟨left, right, sameReputation, differentTarget⟩
    intro sameKernel
    apply differentTarget
    have kernelRelated : Setoid.ker (score ∘ history) left right :=
      sameReputation
    rw [sameKernel] at kernelRelated
    exact kernelRelated

#print axioms reputation_sufficiency_criterion

end D5.S3.ConceptDynamics.Trust.ReputationSufficiencyCriterion
