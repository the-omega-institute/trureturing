/- GID: D5/S3/ConceptDynamics/Governance/JudgmentRelativeAnalogyCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/JudgmentRelativeAnalogyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Similarity supports equal judgments only when it preserves judgment distinctions. -/

import D5.S3.ConceptDynamics.Governance.RuleConstraintDifferenceCriterion
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-23):
   * Exact family hits `Concept`, `Refines`, and `canonicalTargetReadout` model
     the source similarity concept, refinement, and canonical judgment target;
     all are imported and used directly.
   * The unrestricted forward half of the exact repository theorem
     `rule_constraint_difference_criterion` excludes equal-readout pairs with
     unequal decisions and is applied below after projecting the canonical
     target-image factor to its judgment value.
   * `target_sufficient_iff_fiber_constant` is an adjacent exact equivalence,
     but its reverse direction assumes nonempty states. No such unnecessary
     restriction is added here, and no duplicate or `_eq_` bridge is declared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.JudgmentRelativeAnalogyCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Governance.RuleConstraintDifferenceCriterion
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- A similarity concept sufficient for the canonical judgment target makes
judgment constant on every similarity fiber. Conversely, one same-similarity
pair with different judgments publicly witnesses that insufficiency. -/
theorem judgment_relative_analogy_criterion
    {Case Similarity Judgment : Type*}
    (similarity : Concept Case Similarity) (judgment : Case -> Judgment) :
    (Refines (canonicalTargetReadout judgment) similarity ->
      forall x y,
        similarity x = similarity y -> judgment x = judgment y) /\
    ((exists x y,
      similarity x = similarity y /\ judgment x ≠ judgment y) ->
      Not (Refines (canonicalTargetReadout judgment) similarity)) := by
  have noConflict
      (hsufficient : Refines (canonicalTargetReadout judgment) similarity) :
      Not (exists x y,
        similarity x = similarity y /\ judgment x ≠ judgment y) := by
    rcases hsufficient with ⟨factor, hfactor⟩
    apply (rule_constraint_difference_criterion similarity judgment).1
    refine ⟨fun coordinate => (factor coordinate).1, ?_⟩
    funext state
    have hpoint := congrArg Subtype.val (congrFun hfactor state)
    simp only [canonicalTargetReadout] at hpoint
    unfold Function.comp at hpoint ⊢
    exact hpoint
  constructor
  · intro hsufficient x y hsimilar
    by_contra hdifferent
    exact noConflict hsufficient ⟨x, y, hsimilar, hdifferent⟩
  · intro hwitness hsufficient
    exact noConflict hsufficient hwitness

#print axioms judgment_relative_analogy_criterion

end D5.S3.ConceptDynamics.Governance.JudgmentRelativeAnalogyCriterion
