/- GID: D5/S3/ConceptDynamics/Appeal/ExplainableNotContestable
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Appeal/ExplainableNotContestable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A public rule can coexist with an outcome hidden by case and appeal evidence. -/

import D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'explainable_not_contestable' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested search for `contestable`, `explainable`, `appeal`, and
     `rule.*public` found `MinimalAppealLabelCount` and
     `RedundantAppealDefectPersistence`, but no separation theorem.
   * `MinimalAppealLabelCount` gives the exact finite label count needed for
     repair, so it does not duplicate this concrete failure-of-repair witness.
   * `Refines`, `conceptJoin`, `canonicalTargetReadout`, and the redundant-appeal
     obstruction are imported; the remaining proof uses finite Boolean witnesses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Appeal.ExplainableNotContestable

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- A fully public rule: its rule and language coordinates are the same readout. -/
def publicRule : Concept (Bool × Bool) Bool := Prod.fst

/-- The coarse case concept retains only the first state coordinate. -/
def coarseCase : Concept (Bool × Bool) Bool := Prod.fst

/-- No new appeal evidence is represented by a constant readout. -/
def noAppealEvidence : Concept (Bool × Bool) Bool := fun _ => false

/-- The classification target depends on the coordinate hidden from the case concept. -/
def classificationTarget : Bool × Bool → Bool := Prod.snd

/-- There are finite readouts for which the rule factors through the public language,
while the canonical target does not factor through case-plus-appeal evidence. Moreover,
two states have distinct outcomes but identical available evidence. -/
theorem explainable_not_contestable :
    ∃ (ruleReadout languageReadout caseReadout appealReadout :
        Concept (Bool × Bool) Bool) (target : Bool × Bool → Bool),
      Refines ruleReadout languageReadout ∧
        (∀ x y, appealReadout x = appealReadout y) ∧
          ¬Refines (canonicalTargetReadout target)
            (conceptJoin caseReadout appealReadout) ∧
          ∃ x y : Bool × Bool, target x ≠ target y ∧
            conceptJoin caseReadout appealReadout x =
              conceptJoin caseReadout appealReadout y := by
  refine ⟨publicRule, publicRule, coarseCase, noAppealEvidence,
    classificationTarget, ⟨id, rfl⟩, (fun _ _ => rfl), ?_, ?_⟩
  · have htargetDistinct :
        canonicalTargetReadout classificationTarget (false, false) ≠
          canonicalTargetReadout classificationTarget (false, true) := by
      intro hsame
      exact Bool.false_ne_true (congrArg (fun value => value.1) hsame)
    have hresult :=
      redundant_appeal_cannot_repair_structural_defect
        coarseCase noAppealEvidence (canonicalTargetReadout classificationTarget)
        ⟨fun _ => false, rfl⟩
    exact
      (hresult.2.2
        ⟨((false, false), (false, true)), rfl, htargetDistinct⟩).2
  · exact ⟨(false, false), (false, true), Bool.false_ne_true, rfl⟩

example :
    ∃ x y : Bool × Bool,
      classificationTarget x ≠ classificationTarget y ∧
        conceptJoin coarseCase noAppealEvidence x =
          conceptJoin coarseCase noAppealEvidence y := by
  exact ⟨(false, false), (false, true), Bool.false_ne_true, rfl⟩

#print axioms explainable_not_contestable

end D5.S3.ConceptDynamics.Appeal.ExplainableNotContestable
