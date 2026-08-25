/- GID: D5/S3/ConceptDynamics/Appeal/ContestabilityWithoutRuleExplanation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Appeal/ContestabilityWithoutRuleExplanation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact appeals can repair outcomes while the governing rule stays absent from the log. -/

import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-25):
   * `Appeal.ExplainableNotContestable` is the exact opposite independence
     direction and already serves another atom; it does not state `A = T` or
     target sufficiency together with rule-log insufficiency.
   * Searches for contestability without explanation, `appeal = target`, and
     the full three-clause refinement contrast found no exact D5 theorem.
   * `Concept`, `Refines`, `conceptJoin`, `canonicalTargetReadout`, and
     `universal_sufficiency_factorization` are the canonical family primitives
     and the effective-target bridge; all are reused directly.
   * The pinned environment's exact `Bool.false_ne_true` theorem supplies the
     independent rule distinction hidden by the constant explanation log. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Appeal.ContestabilityWithoutRuleExplanation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- An exact review oracle makes the canonical target recoverable from case
and appeal evidence, while an independent nonconstant rule still cannot be
recovered from a constant explanation log. -/
theorem contestable_outcome_can_lack_rule_explanation
    (target : Concept (Bool × Bool) Bool) :
    ∃ rule : Concept (Bool × Bool) Bool,
      ∃ log : Concept (Bool × Bool) Unit,
        ∃ caseReadout : Concept (Bool × Bool) Unit,
          ∃ appeal : Concept (Bool × Bool) Bool,
            appeal = target ∧
              Refines (canonicalTargetReadout target)
                (conceptJoin caseReadout appeal) ∧
              ¬ Refines rule log := by
  refine ⟨Prod.snd, fun _ => (), fun _ => (), target, rfl, ?_, ?_⟩
  · apply
      (universal_sufficiency_factorization
        (conceptJoin (fun _ : Bool × Bool => ()) target) target).2.mpr
    intro left right sameEvidence
    exact congrArg Prod.snd sameEvidence
  · rintro ⟨factor, ruleFactors⟩
    have sameRule :
        (Prod.snd : Bool × Bool → Bool) (false, false) =
          (Prod.snd : Bool × Bool → Bool) (false, true) := by
      rw [ruleFactors]
      rfl
    exact Bool.false_ne_true sameRule

#print axioms contestable_outcome_can_lack_rule_explanation

end D5.S3.ConceptDynamics.Appeal.ContestabilityWithoutRuleExplanation
