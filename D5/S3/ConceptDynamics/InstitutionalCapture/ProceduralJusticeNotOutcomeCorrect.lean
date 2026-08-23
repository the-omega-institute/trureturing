/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Procedural factorization can coexist with unavoidable factual error. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-23):
   * `rg -n -F 'procedural_completeness_permits_wrong_outcome' D5
     Golden/Frozen/accepted` returned no matches.
   * The required `conceptJoin|Refines` and institutional-capture searches found
     the canonical primitives and seven sibling modules, but no procedural-outcome theorem.
   * Searches for procedural correctness, wrong outcomes, joint readouts, and target
     defects found adjacent results `target_recovery_criterion`,
     `redundant_appeal_cannot_repair_structural_defect`, and
     `explainable_not_contestable`; none combines an actual judgment, universal failure,
     and the sufficient-readout contrast required here.
   * This module reuses `Concept`, `Refines`, `conceptJoin`, `defectRelation`, and
     `answerability_criterion`. The last converts the nonempty joint-readout defect into
     the factorization obstruction used below; only Boolean witnesses and equality
     transport remain local.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.ProceduralJusticeNotOutcomeCorrect

open D5.S0.Rewriting.Quotients.AnswerabilityCriterion
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A judgment is procedurally complete when it reads only the public facts-and-rules join. -/
def ProcedurallyComplete
    {Case Fact Rule Verdict : Type*} (facts : Concept Case Fact)
    (rules : Concept Case Rule) (judgment : Concept Case Verdict) : Prop :=
  Refines judgment (conceptJoin facts rules)

/-- A judgment is outcome-correct when it agrees extensionally with the factual truth. -/
def OutcomeCorrect
    {Case Verdict : Type*} (truth judgment : Concept Case Verdict) : Prop :=
  judgment = truth

/-- A nonempty truth defect in the public join forces every procedurally complete
judgment to disagree with truth on at least one case. -/
theorem every_procedurally_complete_judgment_is_incorrect
    {Case Fact Rule Verdict : Type*} (anchor : Case)
    (facts : Concept Case Fact) (rules : Concept Case Rule)
    (truth : Concept Case Verdict)
    (coarse : (defectRelation (conceptJoin facts rules) truth).Nonempty) :
    forall judgment : Concept Case Verdict,
      ProcedurallyComplete facts rules judgment ->
        exists case, judgment case ≠ truth case := by
  intro judgment procedural
  have truthDoesNotRefine :
      Not (Refines truth (conceptJoin facts rules)) := by
    intro truthRefines
    have criterion :=
      answerability_criterion anchor (conceptJoin facts rules) truth
    have factorization :
        exists answer : Fact × Rule -> Verdict,
          truth = answer ∘ conceptJoin facts rules := by
      simpa only [Refines] using truthRefines
    have emptyDefect :
        defectRelation (conceptJoin facts rules) truth = ∅ := by
      simpa only [defectRelation] using criterion.2.2.mpr factorization
    exact coarse.ne_empty emptyDefect
  have incorrect : Not (OutcomeCorrect truth judgment) := by
    intro correct
    apply truthDoesNotRefine
    change Refines judgment (conceptJoin facts rules) at procedural
    change judgment = truth at correct
    rcases procedural with ⟨decide, hdecide⟩
    exact ⟨decide, correct.symm.trans hdecide⟩
  by_contra noError
  apply incorrect
  change judgment = truth
  funext case
  by_contra mismatch
  exact noError ⟨case, mismatch⟩

/-- If the truth factors through the public join, choosing truth itself gives a judgment
that is both procedurally complete and correct. -/
theorem sufficient_joint_readout_permits_correct_outcome
    {Case Fact Rule Verdict : Type*}
    (facts : Concept Case Fact) (rules : Concept Case Rule)
    (truth : Concept Case Verdict)
    (sufficient : Refines truth (conceptJoin facts rules)) :
    exists judgment : Concept Case Verdict,
      ProcedurallyComplete facts rules judgment /\
        OutcomeCorrect truth judgment := by
  exact ⟨truth, sufficient, rfl⟩

/-- There are public facts, rules, truth, and a judgment such that the judgment is
procedurally complete but wrong, and the coarse public join makes every procedurally
complete judgment wrong on some case. -/
theorem procedural_completeness_permits_wrong_outcome :
    exists facts : Concept Bool PUnit,
      exists rules : Concept Bool PUnit,
        exists truth judgment : Concept Bool Bool,
          (defectRelation (conceptJoin facts rules) truth).Nonempty /\
            ProcedurallyComplete facts rules judgment /\
            (exists case, judgment case ≠ truth case) /\
            forall candidate : Concept Bool Bool,
              ProcedurallyComplete facts rules candidate ->
                exists case, candidate case ≠ truth case := by
  let facts : Concept Bool PUnit := fun _ => PUnit.unit
  let rules : Concept Bool PUnit := fun _ => PUnit.unit
  let truth : Concept Bool Bool := id
  let judgment : Concept Bool Bool := fun _ => false
  have coarse :
      (defectRelation (conceptJoin facts rules) truth).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  have procedural : ProcedurallyComplete facts rules judgment :=
    ⟨fun _ => false, rfl⟩
  have wrong := every_procedurally_complete_judgment_is_incorrect
    false facts rules truth coarse judgment procedural
  refine ⟨facts, rules, truth, judgment, coarse, procedural, wrong, ?_⟩
  intro candidate candidateProcedural
  exact every_procedurally_complete_judgment_is_incorrect
    false facts rules truth coarse candidate candidateProcedural

example :
    ProcedurallyComplete (fun _ : Bool => PUnit.unit)
        (fun _ : Bool => PUnit.unit) (fun _ : Bool => false) /\
      Not (OutcomeCorrect (id : Concept Bool Bool) (fun _ : Bool => false)) := by
  constructor
  · exact ⟨fun _ => false, rfl⟩
  · change (fun _ : Bool => false) ≠ (id : Concept Bool Bool)
    intro equality
    exact Bool.false_ne_true (by
      simpa only [id_eq] using congrFun equality true)

#print axioms procedural_completeness_permits_wrong_outcome

end D5.S3.ConceptDynamics.InstitutionalCapture.ProceduralJusticeNotOutcomeCorrect
