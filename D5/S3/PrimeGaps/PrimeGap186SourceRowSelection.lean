/- GID: D5/S3/PrimeGaps/PrimeGap186SourceRowSelection
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formalize the exact source-row selection rule feeding the six PrimeGaps186 physical groups. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

/-!
This module ports the row-selection logic in upstream `build_inputs`:

* outer `h2`: every old/new row of source order < 3;
* outer `h25`: every old/new row of source order = 3;
* old/new inner `h2`: rows of source order = 2 only;
* old/new inner `h25`: rows of source order = 3.

In particular source-order-one rows are used only by the outer `h2` group, while source-order-three
rows are repackaged into effective order `5/2` groups.
-/

namespace D5.S3.PrimeGaps.PrimeGap186SourceRowSelection

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry
open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

/-- Interpret the source-ladder selector `ν` as the old/new family used upstream. -/
def sourcePopulationOfNu (ν : Fin 2) : PhysicalSourcePopulation :=
  if ν = 0 then .oldInner else .newInner

/-- Exact membership predicate for a source row in one of the six coarse groups. -/
def selectedByGroup (g : PhysicalSourceGroup) (ν : Fin 2) (t : ℕ) : Prop :=
  match g with
  | .outerH2 => physicalSourceOrder t < 3
  | .outerH25 => physicalSourceOrder t = 3
  | .oldInnerH2 => ν = 0 ∧ physicalSourceOrder t = 2
  | .oldInnerH25 => ν = 0 ∧ physicalSourceOrder t = 3
  | .newInnerH2 => ν = 1 ∧ physicalSourceOrder t = 2
  | .newInnerH25 => ν = 1 ∧ physicalSourceOrder t = 3

/-- Every source row belongs to exactly one outer group. -/
theorem existsUnique_outer_group (ν : Fin 2) (t : ℕ) :
    ∃! g : PhysicalSourceGroup,
      g.isOuter = true ∧ selectedByGroup g ν t := by
  rcases physicalSourceOrder_mem t with h1 | h2 | h3
  · refine ⟨.outerH2, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h1]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h1] at hgOuter hgSel ⊢
  · refine ⟨.outerH2, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h2]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h2] at hgOuter hgSel ⊢
  · refine ⟨.outerH25, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h3]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h3] at hgOuter hgSel ⊢

/-- Inner source-order-one rows are intentionally excluded by the upstream selection rule. -/
theorem order_one_not_selected_inner
    (ν : Fin 2) (t : ℕ) (h1 : physicalSourceOrder t = 1)
    (g : PhysicalSourceGroup) (hg : g.isOuter = false) :
    ¬ selectedByGroup g ν t := by
  cases g <;> simp [PhysicalSourceGroup.isOuter] at hg
  all_goals simp [selectedByGroup, h1]

/-- Every source-order-two row belongs to exactly one inner group determined by its old/new family. -/
theorem existsUnique_inner_group_order_two
    (ν : Fin 2) (t : ℕ) (h2 : physicalSourceOrder t = 2) :
    ∃! g : PhysicalSourceGroup,
      g.isOuter = false ∧ selectedByGroup g ν t := by
  fin_cases ν
  · refine ⟨.oldInnerH2, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h2]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h2] at hgOuter hgSel ⊢
  · refine ⟨.newInnerH2, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h2]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h2] at hgOuter hgSel ⊢

/-- Every source-order-three row belongs to exactly one inner `h25` group determined by family. -/
theorem existsUnique_inner_group_order_three
    (ν : Fin 2) (t : ℕ) (h3 : physicalSourceOrder t = 3) :
    ∃! g : PhysicalSourceGroup,
      g.isOuter = false ∧ selectedByGroup g ν t := by
  fin_cases ν
  · refine ⟨.oldInnerH25, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h3]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h3] at hgOuter hgSel ⊢
  · refine ⟨.newInnerH25, ?_, ?_⟩
    · simp [PhysicalSourceGroup.isOuter, selectedByGroup, h3]
    · intro g hg
      rcases hg with ⟨hgOuter, hgSel⟩
      cases g <;> simp [PhysicalSourceGroup.isOuter, selectedByGroup, h3] at hgOuter hgSel ⊢

/-- The key repackaging step: every selected source-order-three row is assigned to a coarse group
whose effective order is exactly `5/2`. -/
theorem source_order_three_maps_to_effective_five_halves
    (g : PhysicalSourceGroup) (ν : Fin 2) (t : ℕ)
    (hsel : selectedByGroup g ν t) (h3 : physicalSourceOrder t = 3) :
    g.effectiveOrder = 5 / 2 := by
  cases g <;> simp [selectedByGroup, PhysicalSourceGroup.effectiveOrder, h3] at hsel ⊢

/-- Conversely, a selected coarse `h2` group never contains a source-order-three row. -/
theorem effective_two_excludes_source_order_three
    (g : PhysicalSourceGroup) (ν : Fin 2) (t : ℕ)
    (heff : g.effectiveOrder = 2) (hsel : selectedByGroup g ν t) :
    physicalSourceOrder t ≠ 3 := by
  cases g <;> simp [PhysicalSourceGroup.effectiveOrder, selectedByGroup] at heff hsel ⊢
  all_goals omega

#print axioms selectedByGroup
#print axioms existsUnique_outer_group
#print axioms order_one_not_selected_inner
#print axioms existsUnique_inner_group_order_two
#print axioms existsUnique_inner_group_order_three
#print axioms source_order_three_maps_to_effective_five_halves
#print axioms effective_two_excludes_source_order_three

end D5.S3.PrimeGaps.PrimeGap186SourceRowSelection
