/- GID: D5/S3/ConceptDynamics/GraphColoring/DefectRelationMinimumColoring
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/DefectRelationMinimumColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical defect-relation coloring computes the exact finite repair-label count. -/

import D5.S3.ConceptDynamics.Coding.DefectGraphMinimumColoring
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-25):
   * The frozen predecessor supplies the canonical repair feasibility,
     least-label, and effective fiber-diversity objects; they are reused rather
     than redeclared.
   * Exact repository hit `defectRelation` is the family's canonical target
     defect primitive. The graph adapter below references it directly.
   * Repository searches found no corrected theorem whose graph adapter uses
     that primitive; the predecessor's withdrawn receipt precludes bind-only.
   * Exact pinned-library hits `SimpleGraph.Coloring.mk`,
     `Colorable.chromaticNumber_le`, and `le_chromaticNumber_iff_colorable`
     provide the coloring bridge and are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.DefectRelationMinimumColoring

open D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount
open D5.S3.ConceptDynamics.Coding.DefectGraphMinimumColoring
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- The graph adapter uses the family's canonical target-defect relation. -/
def defectGraph {X C Target : Type*}
    (record : Concept X C) (target : Concept X Target) : SimpleGraph X where
  Adj left right := (left, right) ∈ defectRelation record target
  symm := ⟨fun left right adjacent => by
    change record left = record right ∧ target left ≠ target right at adjacent
    change record right = record left ∧ target right ≠ target left
    exact ⟨adjacent.1.symm, Ne.symm adjacent.2⟩⟩
  loopless := ⟨fun state adjacent => by
    change record state = record state ∧ target state ≠ target state at adjacent
    exact adjacent.2 rfl⟩

/-- Finite repair labels are exactly canonical defect-relation graph colorings,
and their least count equals both the chromatic number and the largest target
diversity in one effective concept fiber. -/
theorem minimum_repair_labels_eq_chromatic_eq_fiber_diversity
    {X C Target : Type*} [Fintype X]
    (record : Concept X C) (target : Concept X Target) :
    (∀ labelCount,
      RepairLabelFeasible record target labelCount ↔
        (defectGraph record target).Colorable labelCount) ∧
    ((minimumRepairLabels record target : ℕ∞) =
      (defectGraph record target).chromaticNumber) ∧
    ((defectGraph record target).chromaticNumber =
      (effectiveWorstFiberDiversity record target : ℕ∞)) := by
  classical
  have coloringIff (labelCount : Nat) :
      RepairLabelFeasible record target labelCount ↔
        (defectGraph record target).Colorable labelCount := by
    constructor
    · rintro ⟨label, determines⟩
      refine ⟨SimpleGraph.Coloring.mk label ?_⟩
      intro left right adjacent sameLabel
      change record left = record right ∧ target left ≠ target right at adjacent
      exact adjacent.2 (determines left right adjacent.1 sameLabel)
    · rintro ⟨coloring⟩
      refine ⟨fun state => coloring state, ?_⟩
      intro left right sameRecord sameColor
      by_contra targetDifferent
      apply (coloring.valid ?_) sameColor
      change record left = record right ∧ target left ≠ target right
      exact ⟨sameRecord, targetDifferent⟩
  letI : Finite (Set.range record) :=
    Finite.of_surjective (Set.rangeFactorization record)
      Set.rangeFactorization_surjective
  letI : Fintype (Set.range record) := Fintype.ofFinite _
  have effectiveBounds :=
    minimal_appeal_label_count (Set.rangeFactorization record) target
  have attainable :
      RepairLabelFeasible record target
        (effectiveWorstFiberDiversity record target) := by
    rcases effectiveBounds.1 with ⟨label, determines⟩
    refine ⟨label, ?_⟩
    intro left right sameRecord sameLabel
    apply determines left right
    · exact Subtype.ext sameRecord
    · exact sameLabel
  have lowerBound {labelCount : Nat} (label : X → Fin labelCount)
      (determines : AppealDetermines record target label) :
      effectiveWorstFiberDiversity record target ≤ labelCount := by
    apply effectiveBounds.2 label
    intro left right sameEffectiveValue sameLabel
    apply determines left right
    · exact congrArg Subtype.val sameEffectiveValue
    · exact sameLabel
  have minimumEq :
      minimumRepairLabels record target =
        effectiveWorstFiberDiversity record target := by
    unfold minimumRepairLabels
    apply Nat.le_antisymm
    · exact Nat.find_min' _ attainable
    · rcases Nat.find_spec
        (show ∃ labelCount, RepairLabelFeasible record target labelCount from
          ⟨_, attainable⟩) with
        ⟨label, determines⟩
      exact lowerBound label determines
  have chromaticEq :
      (defectGraph record target).chromaticNumber =
        (effectiveWorstFiberDiversity record target : ℕ∞) := by
    apply le_antisymm
    · exact ((coloringIff _).1 attainable).chromaticNumber_le
    · rw [SimpleGraph.le_chromaticNumber_iff_colorable]
      intro labelCount colorable
      rcases (coloringIff labelCount).2 colorable with ⟨label, determines⟩
      exact_mod_cast lowerBound label determines
  refine ⟨coloringIff, ?_, chromaticEq⟩
  rw [minimumEq, chromaticEq]

#print axioms minimum_repair_labels_eq_chromatic_eq_fiber_diversity

end D5.S3.ConceptDynamics.GraphColoring.DefectRelationMinimumColoring
