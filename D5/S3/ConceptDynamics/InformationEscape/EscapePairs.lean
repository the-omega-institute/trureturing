/- GID: D5/S3/ConceptDynamics/InformationEscape/EscapePairs
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/EscapePairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite escape pairs decompose into full-catalog and unique-capture parts. -/

import D5.S3.ConceptDynamics.CIRPT.RoleSignature
import D5.S3.ConceptDynamics.InformationEscape.CatalogKernel
import Mathlib.Data.Finset.SDiff

/- Library-search audit trail (2026-09-04):
   * Repository searches for `escapePairs`, `uniqueCapturePairs`, and their
     insertion and difference laws found no existing declarations under `D5`.
   * Exact current-tree hit `CIRPT.offDiagonalPairs` is reused on
     `arena.State`; no arena-specific copy is introduced. Exact hits
     `Catalog.indistinguishable_mono` and `indistinguishable_insert_iff`
     supply the selected-catalog order and insertion steps.
   * Pinned Mathlib exact hits `Finset.union_sdiff_of_subset`,
     `Finset.disjoint_sdiff`, and finite-filter membership supply the
     decomposition. No duplicate finite-set difference law is proved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

/-- Ordered distinct state pairs left indistinguishable by a selected catalog. -/
def escapePairs {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (offDiagonalPairs arena.State).filter fun pair =>
    catalog.indistinguishable selected pair.1 pair.2

/-- Pairs captured by one theorem and by no theorem in its leave-one-out catalog. -/
def uniqueCapturePairs {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Finset (arena.State × arena.State) := by
  letI := arena.stateDecidableEq
  exact (catalog.escapePairs (catalog.without index)).filter fun pair =>
    ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2

private theorem insert_without_eq_full
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    let _ := catalog.indexDecidableEq
    insert index (catalog.without index) = catalog.fullIndexSet := by
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  ext candidate
  by_cases same : candidate = index <;>
    simp [Catalog.mem_without_iff, fullIndexSet, same]

/-- Unique captures are exactly the leave-one-out escape pairs removed by the full catalog. -/
theorem uniqueCapturePairs_eq_sdiff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.uniqueCapturePairs index =
      catalog.escapePairs (catalog.without index) \
        catalog.escapePairs catalog.fullIndexSet := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  have inserted := insert_without_eq_full catalog index
  ext pair
  simp only [uniqueCapturePairs, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨leaveOneOut, separated⟩
    refine ⟨leaveOneOut, ?_⟩
    intro fullEscape
    have fullAgreement := (Finset.mem_filter.mp fullEscape).2
    rw [← inserted] at fullAgreement
    exact separated
      ((catalog.indistinguishable_insert_iff
        (catalog.without index) index pair.1 pair.2).mp fullAgreement).1
  · rintro ⟨leaveOneOut, notFullEscape⟩
    refine ⟨leaveOneOut, ?_⟩
    intro indexAgreement
    apply notFullEscape
    have leaveOneOutParts := Finset.mem_filter.mp leaveOneOut
    apply Finset.mem_filter.mpr
    refine ⟨leaveOneOutParts.1, ?_⟩
    rw [← inserted]
    exact (catalog.indistinguishable_insert_iff
      (catalog.without index) index pair.1 pair.2).mpr
        ⟨indexAgreement, leaveOneOutParts.2⟩

/-- IE-002: adding selected theorems can only remove escape pairs. -/
theorem escapePairs_anti
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {smaller larger : Finset catalog.Index} (subset : smaller ⊆ larger) :
    catalog.escapePairs larger ⊆ catalog.escapePairs smaller := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  intro pair pairInLarger
  have parts := Finset.mem_filter.mp pairInLarger
  apply Finset.mem_filter.mpr
  exact ⟨parts.1, catalog.indistinguishable_mono subset parts.2⟩

/-- IE-004: inserting one theorem filters by exactly that theorem's agreement kernel. -/
theorem escapePairs_insert
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (selected : Finset catalog.Index) :
    catalog.escapePairs (let _ := catalog.indexDecidableEq; insert index selected) =
      (catalog.escapePairs selected).filter fun pair =>
        (catalog.theoremAt index).primitives.agrees pair.1 pair.2 := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  letI := catalog.indexDecidableEq
  ext pair
  simp only [escapePairs, Finset.mem_filter]
  rw [catalog.indistinguishable_insert_iff selected index pair.1 pair.2]
  tauto

/-- IE-005: every full-catalog escape also survives removal of one theorem. -/
theorem escapePairs_full_subset_without
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.escapePairs catalog.fullIndexSet ⊆
      catalog.escapePairs (catalog.without index) := by
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  apply catalog.escapePairs_anti
  intro candidate _
  exact Finset.mem_univ candidate

/-- IE-006: leave-one-out escape is the union of persistent and uniquely captured pairs. -/
theorem escapePairs_without_eq_union
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.escapePairs (catalog.without index) =
      catalog.escapePairs catalog.fullIndexSet ∪
        catalog.uniqueCapturePairs index := by
  rw [catalog.uniqueCapturePairs_eq_sdiff index]
  exact (Finset.union_sdiff_of_subset
    (catalog.escapePairs_full_subset_without index)).symm

/-- The two parts of the leave-one-out escape decomposition are disjoint. -/
theorem escapePairs_full_disjoint_uniqueCapturePairs
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    Disjoint (catalog.escapePairs catalog.fullIndexSet)
      (catalog.uniqueCapturePairs index) := by
  rw [catalog.uniqueCapturePairs_eq_sdiff index]
  exact Finset.disjoint_sdiff

end Catalog

private abbrev escapeFixtureArena : Arena :=
  Arena.ofFintype (Bool × Bool)

private abbrev firstCoordinateBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.fst⟩

private abbrev secondCoordinateBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.snd⟩

private abbrev firstCoordinateUnit : TheoremUnit escapeFixtureArena where
  primitives := firstCoordinateBundle
  Statement := True
  proof := True.intro

private abbrev secondCoordinateUnit : TheoremUnit escapeFixtureArena where
  primitives := secondCoordinateBundle
  Statement := True
  proof := True.intro

private def escapeFixtureCatalog : Catalog escapeFixtureArena where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt
    | false => firstCoordinateUnit
    | true => secondCoordinateUnit

/- The two coordinate kernels jointly separate every distinct Boolean pair. -/
example :
    escapeFixtureCatalog.escapePairs escapeFixtureCatalog.fullIndexSet = ∅ := by
  decide

/- Each coordinate uniquely captures four ordered pairs. -/
example : (escapeFixtureCatalog.uniqueCapturePairs false).card = 4 := by
  decide

example : (escapeFixtureCatalog.uniqueCapturePairs true).card = 4 := by
  decide

end D5.S3.ConceptDynamics.InformationEscape
