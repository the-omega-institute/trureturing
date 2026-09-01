/- GID: D5/S3/ConceptDynamics/Appeal/RuleCoupledAppealContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Appeal/RuleCoupledAppealContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A rule-coupled appeal can recover the target while the log omits the rule. -/

import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-25):
   * The frozen `ContestabilityWithoutRuleExplanation` is the retracted separable
     construction: its appeal is chosen independently as the target.
   * The opposite-direction `ExplainableNotContestable` does not state this atom.
   * `Concept`, `Refines`, `conceptJoin`, `canonicalTargetReadout`, and
     `universal_sufficiency_factorization` are the canonical family primitives and
     are imported rather than redeclared.
   * A body-shape search for equality-test oracles composed with both orders of a
     rule/case join found no existing D5 construction.
   * Pinned Mathlib supplies equality symmetry, but no exact theorem combining the
     appeal-target construction, target recovery, and missing rule explanation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Appeal.RuleCoupledAppealContrast

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Appeal evidence and the repaired target are computed in opposite orders from
the same case/rule pair. Their equality and target sufficiency therefore use the
same nonconstant rule that the constant explanation log cannot recover. -/
theorem rule_coupled_appeal_can_repair_without_log_explanation :
    ∃ rule : Concept (Bool × Bool) Bool,
      ∃ log : Concept (Bool × Bool) Unit,
        ∃ caseReadout : Concept (Bool × Bool) Bool,
          ∃ appealOracle : Bool × Bool → Bool,
            ∃ targetOracle : Bool × Bool → Bool,
              appealOracle ∘ conceptJoin rule caseReadout =
                  targetOracle ∘ conceptJoin caseReadout rule ∧
                Refines
                  (canonicalTargetReadout
                    (targetOracle ∘ conceptJoin caseReadout rule))
                  (conceptJoin caseReadout
                    (appealOracle ∘ conceptJoin rule caseReadout)) ∧
                ¬ Refines rule log := by
  let rule : Concept (Bool × Bool) Bool := Prod.snd
  let log : Concept (Bool × Bool) Unit := fun _ => ()
  let caseReadout : Concept (Bool × Bool) Bool := Prod.fst
  let appealOracle : Bool × Bool → Bool :=
    fun evidence => if evidence.1 then evidence.2 else !evidence.2
  let targetOracle : Bool × Bool → Bool :=
    fun evidence => if evidence.1 then evidence.2 else !evidence.2
  let appeal := appealOracle ∘ conceptJoin rule caseReadout
  let target := targetOracle ∘ conceptJoin caseReadout rule
  have appealEqualsTarget : appeal = target := by
    funext state
    simp only [appeal, target, appealOracle, targetOracle, rule, caseReadout]
    unfold Function.comp conceptJoin
    rcases state with ⟨ruleValue, caseValue⟩
    cases ruleValue <;> cases caseValue <;> rfl
  refine ⟨rule, log, caseReadout, appealOracle, targetOracle,
    appealEqualsTarget, ?_, ?_⟩
  · apply
      (universal_sufficiency_factorization
        (conceptJoin caseReadout appeal) target).2.mpr
    intro left right sameEvidence
    have sameAppeal : appeal left = appeal right :=
      congrArg Prod.snd sameEvidence
    calc
      target left = appeal left := congrFun appealEqualsTarget.symm left
      _ = appeal right := sameAppeal
      _ = target right := congrFun appealEqualsTarget right
  · rintro ⟨factorThroughLog, ruleFactors⟩
    have sameRule : rule (false, false) = rule (false, true) := by
      rw [ruleFactors]
      rfl
    exact Bool.false_ne_true sameRule

#print axioms rule_coupled_appeal_can_repair_without_log_explanation

end D5.S3.ConceptDynamics.Appeal.RuleCoupledAppealContrast
