/- GID: D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Record-determined appeal evidence cannot repair a target defect. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-21):
   * Exact repository hits `Concept`, `Refines`, `conceptJoin`,
     `concept_join_universal`, and `defectRelation` are the frozen family
     primitives for the source concept order, join, and target defect. They are
     imported and applied directly rather than redeclared.
   * Repository searches found no theorem packaging appeal equivalence,
     unchanged distinctions, defect persistence, and failed target
     factorization. `PrecedentTargetCompletion` concerns a different circular
     target-completion problem.
   * Pinned Mathlib exact hits `Prod.ext` and `congrArg` provide pair equality
     and equality transport and are applied directly.
   * `Function.FactorsThrough` is adjacent, but the frozen family's `Refines`
     relation is the canonical abstraction. No exact appeal theorem was found.
   * `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Two concepts have the same distinction power when each factors through the
other. -/
def ConceptEquivalent {X C D : Type*}
    (left : Concept X C) (right : Concept X D) : Prop :=
  Refines left right ∧ Refines right left

/-- If every permitted appeal signal is already determined by the original
case record, then joining it to the record changes no distinctions. Any
nonempty target defect persists, so the target still cannot factor through the
appeal interface and full appeal capability is absent. -/
theorem redundant_appeal_cannot_repair_structural_defect
    {X CaseRecord AppealEvidence Outcome : Type*}
    (record : Concept X CaseRecord)
    (appeal : Concept X AppealEvidence)
    (target : Concept X Outcome)
    (appealDeterminedByRecord : Refines appeal record) :
    ConceptEquivalent (conceptJoin record appeal) record ∧
    (∀ x y, conceptJoin record appeal x = conceptJoin record appeal y ↔
      record x = record y) ∧
    ((defectRelation record target).Nonempty →
      (defectRelation (conceptJoin record appeal) target).Nonempty ∧
      ¬Refines target (conceptJoin record appeal)) := by
  rcases appealDeterminedByRecord with ⟨appealFactor, happeal⟩
  have hrecordRefinesJoin : Refines record (conceptJoin record appeal) :=
    (concept_join_universal record appeal record).1
  have happealRefinesRecord : Refines appeal record :=
    ⟨appealFactor, happeal⟩
  have hjoinRefinesRecord : Refines (conceptJoin record appeal) record :=
    (concept_join_universal record appeal record).2.2
      ⟨id, rfl⟩ happealRefinesRecord
  have hsame : ∀ x y,
      conceptJoin record appeal x = conceptJoin record appeal y ↔
        record x = record y := by
    intro x y
    constructor
    · intro hjoin
      exact congrArg Prod.fst hjoin
    · intro hrecord
      change (record x, appeal x) = (record y, appeal y)
      apply Prod.ext hrecord
      rw [happeal]
      exact congrArg appealFactor hrecord
  refine ⟨⟨hjoinRefinesRecord, hrecordRefinesJoin⟩, hsame, ?_⟩
  intro hdefect
  rcases hdefect with ⟨⟨x, y⟩, hrecord, htarget⟩
  have hjoinedDefect :
      (defectRelation (conceptJoin record appeal) target).Nonempty :=
    ⟨(x, y), (hsame x y).2 hrecord, htarget⟩
  refine ⟨hjoinedDefect, ?_⟩
  rintro ⟨targetFactor, htargetFactor⟩
  apply htarget
  rw [htargetFactor]
  exact congrArg targetFactor ((hsame x y).2 hrecord)

/-- A constant case record and constant permitted appeal signal leave the
identity target defect unrepaired. -/
example :
    let record : Concept Bool Unit := fun _ => ()
    let appeal : Concept Bool Bool := fun _ => false
    let target : Concept Bool Bool := id
    ¬Refines target (conceptJoin record appeal) := by
  dsimp
  have hresult := redundant_appeal_cannot_repair_structural_defect
    (fun _ : Bool => ()) (fun _ : Bool => false) (id : Concept Bool Bool)
    ⟨fun _ => false, rfl⟩
  exact (hresult.2.2 ⟨(false, true), rfl, Bool.false_ne_true⟩).2

#print axioms redundant_appeal_cannot_repair_structural_defect

end D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
