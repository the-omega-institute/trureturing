/- GID: D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Defect-graph coloring computes the exact finite repair-label count. -/

import D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/- Library-search audit trail (2026-08-25):
   * Exact family hits `AppealDetermines`, `fiberTargetValues`,
     `worstFiberDiversity`, and `minimal_appeal_label_count` supply the source
     repair test, fiber image, fiber maximum, and sharp label bounds.
   * Repository and accepted-ledger searches found no defect graph or theorem
     connecting its chromatic number to the minimum repair-label count.
   * Exact pinned-library hits `SimpleGraph.Coloring.mk`,
     `Colorable.chromaticNumber_le`, and `le_chromaticNumber_iff_colorable`
     provide the graph-coloring bridge and are applied directly below.
   * `Set.rangeFactorization` is the canonical effective concept readout. It
     keeps the theorem at the source's finite-state scope without requiring the
     raw concept codomain or target codomain to be finite. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.DefectGraphMinimumColoring

open D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The defect graph joins states in one concept fiber exactly when their
target values differ. -/
def defectGraph {X C Target : Type*}
    (record : Concept X C) (target : Concept X Target) : SimpleGraph X where
  Adj left right := record left = record right ∧ target left ≠ target right
  symm := ⟨fun _left _right adjacent =>
    ⟨adjacent.1.symm, Ne.symm adjacent.2⟩⟩
  loopless := ⟨fun _state adjacent => adjacent.2 rfl⟩

/-- A finite label alphabet is feasible when its labels determine the target
inside every fiber of the original concept. -/
def RepairLabelFeasible {X C Target : Type*}
    (record : Concept X C) (target : Concept X Target) (labelCount : Nat) : Prop :=
  ∃ label : X → Fin labelCount, AppealDetermines record target label

private theorem repair_label_feasible_exists
    {X C Target : Type*} [Finite X]
    (record : Concept X C) (target : Concept X Target) :
    ∃ labelCount, RepairLabelFeasible record target labelCount := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let label : X → Fin (Fintype.card X) := Fintype.equivFin X
  refine ⟨Fintype.card X, label, ?_⟩
  intro left right _ sameLabel
  exact congrArg target ((Fintype.equivFin X).injective sameLabel)

/-- The least label count is selected from the source feasibility test, not
from either the chromatic-number or fiber-diversity conclusion. -/
noncomputable def minimumRepairLabels
    {X C Target : Type*} [Fintype X]
    (record : Concept X C) (target : Concept X Target) : Nat := by
  classical
  exact Nat.find (repair_label_feasible_exists record target)

/-- Maximum target diversity over the canonical effective concept values. -/
noncomputable def effectiveWorstFiberDiversity
    {X C Target : Type*} [Fintype X]
    (record : Concept X C) (target : Concept X Target) : Nat := by
  letI : Finite (Set.range record) :=
    Finite.of_surjective (Set.rangeFactorization record)
      Set.rangeFactorization_surjective
  letI : Fintype (Set.range record) := Fintype.ofFinite _
  exact worstFiberDiversity (Set.rangeFactorization record) target

/-- Finite repair labels are exactly defect-graph colorings, and their least
count is both the graph's chromatic number and the largest target diversity in
one effective concept fiber. -/
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
      exact (coloring.valid ⟨sameRecord, targetDifferent⟩) sameColor
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
    · rcases Nat.find_spec (repair_label_feasible_exists record target) with
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

end D5.S3.ConceptDynamics.Coding.DefectGraphMinimumColoring
