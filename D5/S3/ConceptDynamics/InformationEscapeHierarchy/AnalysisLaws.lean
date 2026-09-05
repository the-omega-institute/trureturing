/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Shared-arena capture, overlap, refinement, spectrum, and role-histogram laws. -/

import D5.S3.ConceptDynamics.InformationEscape.RoleHistogram
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card

/- Library-search audit trail (2026-09-05):
   * Repository searches for `capturePairs`, `captureMultiplicity`,
     `captureSpectrum`, `pairwiseCaptureOverlap`, and `KernelRefines` found no
     landed catalog-level definitions. Exact frozen hits
     `Catalog.uniqueCapturePairs_eq_sdiff`, `escapePairs_anti`,
     `roleHistogram_sum_eq_uniqueCaptureCount`, and
     `catalogIrredundant_iff_forall_pos` are reused.
   * The existing `CIRPT.offDiagonalPairs`, `Catalog.escapePairs`,
     `Catalog.uniqueCapturePairs`, and `Catalog.without` remain the sole
      finite pair and leave-one-out sources; this module introduces no copy.
   * Pinned Mathlib exact hits `Finset.card_eq_sum_card_fiberwise`,
     `Finset.sum_card_fiberwise_eq_card_filter`, `Finset.card_biUnion`, and
     `Finset.card_biUnion_le` supply the finite partition/counting steps.
     Searches found no theorem specializing the first or second factorial
     moment to filtered Finset fibers, so those incidence rearrangements are
     proved locally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT
open scoped BigOperators

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog
def capturePairs {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Finset (arena.State × arena.State) := by
  exact offDiagonalPairs arena.State \
    catalog.escapePairs ({index} : Finset catalog.Index)
def exclusiveCaptureVector {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : catalog.Index -> Nat :=
  fun index => catalog.uniqueCaptureCount index
def pairwiseCaptureOverlapPairs {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    Finset (arena.State × arena.State) := by
  exact catalog.capturePairs left ∩ catalog.capturePairs right
def pairwiseCaptureOverlapCount {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) : Nat :=
  (catalog.pairwiseCaptureOverlapPairs left right).card
def pairwiseCaptureOverlapRate {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) : Rat :=
  (catalog.pairwiseCaptureOverlapCount left right : Rat) /
    (escapeDenominator arena : Rat)
def roleSignatureRate {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (signature : Fin 4 -> Bool) : Rat :=
  (catalog.roleHistogram index signature : Rat) / (escapeDenominator arena : Rat)
def KernelRefines {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (finer coarser : catalog.Index) : Prop :=
  ∀ left right,
    (catalog.theoremAt finer).primitives.agrees left right ->
      (catalog.theoremAt coarser).primitives.agrees left right
def KernelEquivalent {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) : Prop :=
  catalog.KernelRefines left right ∧ catalog.KernelRefines right left

instance kernelRefinesDecidable {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index) :
    Decidable (catalog.KernelRefines finer coarser) := by
  unfold KernelRefines
  infer_instance
inductive KernelComparison
  | equal
  | strictlyFiner
  | strictlyCoarser
  | incomparable
  deriving DecidableEq, Repr
def kernelComparison {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    KernelComparison :=
  if catalog.KernelRefines left right then
    if catalog.KernelRefines right left then .equal else .strictlyFiner
  else if catalog.KernelRefines right left then .strictlyCoarser
  else .incomparable
noncomputable def refinementWitness? {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index) :
    Option (arena.State × arena.State) := by
  exact ((Finset.univ : Finset (arena.State × arena.State)).filter fun pair =>
    (catalog.theoremAt finer).primitives.agrees pair.1 pair.2 ∧
      ¬(catalog.theoremAt coarser).primitives.agrees pair.1 pair.2).toList.head?
theorem refinementWitness?_eq_none_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index) :
    catalog.refinementWitness? finer coarser = none ↔
      catalog.KernelRefines finer coarser := by
  simp only [refinementWitness?, KernelRefines, List.head?_eq_none_iff,
    Finset.toList_eq_nil, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  push Not
  constructor
  · intro h left right agrees; exact h (x := (left, right)) agrees
  · intro h pair agrees; exact h pair.1 pair.2 agrees
theorem refinementWitness?_eq_some_implies {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index)
    (pair : arena.State × arena.State)
    (found : catalog.refinementWitness? finer coarser = some pair) :
    (catalog.theoremAt finer).primitives.agrees pair.1 pair.2 ∧
      ¬(catalog.theoremAt coarser).primitives.agrees pair.1 pair.2 := by
  unfold refinementWitness? at found
  obtain ⟨tail, listEq⟩ := List.head?_eq_some_iff.mp found
  have memList : pair ∈ (((Finset.univ : Finset (arena.State × arena.State)).filter fun p =>
      (catalog.theoremAt finer).primitives.agrees p.1 p.2 ∧
        ¬(catalog.theoremAt coarser).primitives.agrees p.1 p.2).toList) := by
    rw [listEq]; exact List.mem_cons_self
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp memList)).2
theorem refinementWitness?_exists_iff_not_kernelRefines {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index) :
    (∃ pair, catalog.refinementWitness? finer coarser = some pair) ↔
      ¬catalog.KernelRefines finer coarser := by
  rw [← not_congr (catalog.refinementWitness?_eq_none_iff finer coarser)]
  cases h : catalog.refinementWitness? finer coarser <;> simp [h]
theorem kernelComparison_spec {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    (catalog.kernelComparison left right = .equal ↔
      catalog.KernelRefines left right ∧ catalog.KernelRefines right left) ∧
    (catalog.kernelComparison left right = .strictlyFiner ↔
      catalog.KernelRefines left right ∧
        ∃ pair, catalog.refinementWitness? right left = some pair) ∧
    (catalog.kernelComparison left right = .strictlyCoarser ↔
      (∃ pair, catalog.refinementWitness? left right = some pair) ∧
        catalog.KernelRefines right left) ∧
    (catalog.kernelComparison left right = .incomparable ↔
      (∃ pair, catalog.refinementWitness? left right = some pair) ∧
        ∃ pair, catalog.refinementWitness? right left = some pair) := by
  unfold kernelComparison
  rw [catalog.refinementWitness?_exists_iff_not_kernelRefines left right,
    catalog.refinementWitness?_exists_iff_not_kernelRefines right left]
  by_cases forward : catalog.KernelRefines left right <;>
    by_cases reverse : catalog.KernelRefines right left <;> simp [forward, reverse]
def captureMultiplicity {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena)
    (pair : arena.State × arena.State) : Nat := by
  exact ((Finset.univ : Finset catalog.Index).filter fun index =>
    pair ∈ catalog.capturePairs index).card

private def captureMultiplicityFin {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena)
    (pair : arena.State × arena.State) :
    Fin (@Fintype.card catalog.Index catalog.indexFintype + 1) := by
  refine ⟨catalog.captureMultiplicity pair, Nat.lt_succ_of_le ?_⟩
  exact Finset.card_filter_le _ _
def captureSpectrum {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    Fin (@Fintype.card catalog.Index catalog.indexFintype + 1) -> Nat := by
  exact fun multiplicity =>
    ((offDiagonalPairs arena.State).filter fun pair =>
      captureMultiplicityFin catalog pair = multiplicity).card
def captureMultiplicityOne {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) [Nonempty catalog.Index] :
    Fin (@Fintype.card catalog.Index catalog.indexFintype + 1) :=
  ⟨1, Nat.succ_lt_succ (Fintype.card_pos_iff.mpr inferInstance)⟩
def orderedDistinctOverlapTotal {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Nat := by
  exact ∑ left : catalog.Index,
    ∑ right ∈ (Finset.univ : Finset catalog.Index).erase left,
      catalog.pairwiseCaptureOverlapCount left right
def captureSpectrumSecondFactorialMoment {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Nat := by
  exact ∑ multiplicity :
      Fin (@Fintype.card catalog.Index catalog.indexFintype + 1),
    multiplicity.1 * (multiplicity.1 - 1) *
      catalog.captureSpectrum multiplicity
def roleHistogramTotal {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (signature : Fin 4 -> Bool) : Nat := by
  exact ∑ index, catalog.roleHistogram index signature
def roleProfileEq {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) : Prop :=
  ∀ signature, catalog.roleHistogram left signature =
    catalog.roleHistogram right signature
def roleHistogramDifference {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index)
    (signature : Fin 4 -> Bool) : Int :=
  (catalog.roleHistogram left signature : Int) -
    (catalog.roleHistogram right signature : Int)
theorem roleHistogramDifference_eq_zero_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index)
    (signature : Fin 4 -> Bool) :
    catalog.roleHistogramDifference left right signature = 0 ↔
      catalog.roleHistogram left signature = catalog.roleHistogram right signature := by
  simp only [roleHistogramDifference, sub_eq_zero, Int.ofNat_inj]
theorem roleProfileEq_iff_difference_zero {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    catalog.roleProfileEq left right ↔
      ∀ signature, catalog.roleHistogramDifference left right signature = 0 := by
  simp only [roleProfileEq, roleHistogramDifference, sub_eq_zero, Int.ofNat_inj]
def redundantIndices {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Finset catalog.Index := by
  exact Finset.univ.filter fun index => catalog.uniqueCaptureCount index = 0
def CatalogRedundant {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Prop :=
  ∃ index, catalog.uniqueCaptureCount index = 0

private theorem mem_capturePairs_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (index : catalog.Index)
    (pair : arena.State × arena.State) :
    pair ∈ catalog.capturePairs index ↔
      pair.1 ≠ pair.2 ∧
        ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2 := by
  rw [capturePairs, Finset.mem_sdiff]
  constructor
  · rintro ⟨offDiagonal, notEscape⟩
    refine ⟨by simpa [offDiagonalPairs] using offDiagonal, ?_⟩
    intro agrees
    apply notEscape
    apply Finset.mem_filter.mpr
    refine ⟨offDiagonal, (catalog.indistinguishable_iff_forall
      ({index} : Finset catalog.Index) pair.1 pair.2).mpr ?_⟩
    intro candidate candidateMem
    have same : candidate = index := Finset.mem_singleton.mp candidateMem
    simpa [same] using agrees
  · rintro ⟨distinct, separates⟩
    refine ⟨by simpa [offDiagonalPairs] using distinct, ?_⟩
    intro escaped
    exact separates ((catalog.indistinguishable_iff_forall
      ({index} : Finset catalog.Index) pair.1 pair.2).mp
        (Finset.mem_filter.mp escaped).2 index (by simp))

private theorem mem_uniqueCapturePairs_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (index : catalog.Index)
    (pair : arena.State × arena.State) :
    pair ∈ catalog.uniqueCapturePairs index ↔
      pair ∈ catalog.capturePairs index ∧
        ∀ candidate, candidate ≠ index ->
          pair ∉ catalog.capturePairs candidate := by
  rw [mem_capturePairs_iff]
  simp only [InformationEscape.Catalog.uniqueCapturePairs, Finset.mem_filter,
    InformationEscape.Catalog.escapePairs, Catalog.indistinguishable_iff_forall,
    Finset.mem_univ, true_and, Catalog.mem_without_iff]
  constructor
  · rintro ⟨⟨distinct, agreesOthers⟩, separates⟩
    refine ⟨⟨by simpa [offDiagonalPairs] using distinct, separates⟩, ?_⟩
    intro candidate different captured
    exact (mem_capturePairs_iff catalog candidate pair).mp captured |>.2
      (agreesOthers candidate different)
  · rintro ⟨⟨distinct, separates⟩, noOtherCapture⟩
    refine ⟨⟨by simpa [offDiagonalPairs] using distinct, ?_⟩, separates⟩
    intro candidate different
    by_contra separated
    exact noOtherCapture candidate different
      ((mem_capturePairs_iff catalog candidate pair).mpr
        ⟨distinct, separated⟩)
theorem uniqueCapturePairs_eq_capture_sdiff_iUnion
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.uniqueCapturePairs index =
      catalog.capturePairs index \
        ((Finset.univ.erase index).biUnion fun candidate =>
          catalog.capturePairs candidate) := by
  ext pair
  rw [mem_uniqueCapturePairs_iff]
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_erase,
    Finset.mem_univ, and_true, not_exists, not_and]
theorem uniqueCapturePairs_pairwise_disjoint
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {left right : catalog.Index} (different : left ≠ right) :
    Disjoint (catalog.uniqueCapturePairs left)
      (catalog.uniqueCapturePairs right) := by
  rw [Finset.disjoint_left]
  intro pair inLeft inRight
  have leftParts := (mem_uniqueCapturePairs_iff catalog left pair).mp inLeft
  have rightParts := (mem_uniqueCapturePairs_iff catalog right pair).mp inRight
  exact leftParts.2 right different.symm rightParts.1

private theorem uniqueCapturePairs_subset_capturedFull
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.uniqueCapturePairs index ⊆
      offDiagonalPairs arena.State \
        catalog.escapePairs catalog.fullIndexSet := by
  intro pair captured
  have uniqueParts :=
    (mem_uniqueCapturePairs_iff catalog index pair).mp captured
  have captureParts := (mem_capturePairs_iff catalog index pair).mp uniqueParts.1
  apply Finset.mem_sdiff.mpr
  refine ⟨by simpa [offDiagonalPairs] using captureParts.1, ?_⟩
  intro fullEscape
  have fullAgreement := (Finset.mem_filter.mp fullEscape).2
  exact captureParts.2
    ((catalog.indistinguishable_iff_forall catalog.fullIndexSet
      pair.1 pair.2).mp fullAgreement index (Finset.mem_univ index))
theorem sum_uniqueCaptureCount_le_capturedCount
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (∑ index : catalog.Index, catalog.uniqueCaptureCount index) ≤
      (offDiagonalPairs arena.State \
        catalog.escapePairs catalog.fullIndexSet).card := by
  let allUnique := (Finset.univ : Finset catalog.Index).biUnion fun index =>
    catalog.uniqueCapturePairs index
  have pairwise : ((Finset.univ : Finset catalog.Index) : Set catalog.Index).PairwiseDisjoint
      fun index => catalog.uniqueCapturePairs index := by
    intro left _ right _ different
    exact catalog.uniqueCapturePairs_pairwise_disjoint different
  have subset : allUnique ⊆
      offDiagonalPairs arena.State \
        catalog.escapePairs catalog.fullIndexSet := by
    intro pair pairMem
    obtain ⟨index, _, captured⟩ := Finset.mem_biUnion.mp pairMem
    exact catalog.uniqueCapturePairs_subset_capturedFull index captured
  unfold uniqueCaptureCount
  rw [← Finset.card_biUnion pairwise]
  exact Finset.card_le_card subset
theorem pairwiseCaptureOverlap_comm {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    catalog.pairwiseCaptureOverlapPairs left right =
      catalog.pairwiseCaptureOverlapPairs right left := by
  exact Finset.inter_comm _ _
theorem pairwiseCaptureOverlap_diag {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (index : catalog.Index) :
    catalog.pairwiseCaptureOverlapPairs index index =
      catalog.capturePairs index := by
  exact Finset.inter_self _
theorem pairwiseCaptureOverlap_subset {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    catalog.pairwiseCaptureOverlapPairs left right ⊆ catalog.capturePairs left ∧
      catalog.pairwiseCaptureOverlapPairs left right ⊆ catalog.capturePairs right := by
  exact ⟨Finset.inter_subset_left, Finset.inter_subset_right⟩
theorem pairwiseCaptureOverlapCount_le {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    catalog.pairwiseCaptureOverlapCount left right ≤ (catalog.capturePairs left).card ∧
      catalog.pairwiseCaptureOverlapCount left right ≤ (catalog.capturePairs right).card := by
  exact ⟨Finset.card_le_card Finset.inter_subset_left,
    Finset.card_le_card Finset.inter_subset_right⟩
theorem kernelRefines_preorder {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    (∀ index, catalog.KernelRefines index index) ∧
      (∀ first second third,
        catalog.KernelRefines first second ->
        catalog.KernelRefines second third ->
        catalog.KernelRefines first third) := by
  constructor
  · intro index left right agrees
    exact agrees
  · intro first second third firstSecond secondThird left right agrees
    exact secondThird left right (firstSecond left right agrees)
theorem kernelRefines_iff_capturePairs_subset {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index) :
    catalog.KernelRefines finer coarser ↔
      catalog.capturePairs coarser ⊆ catalog.capturePairs finer := by
  constructor
  · intro refines pair coarseCapture
    have coarseParts := (mem_capturePairs_iff catalog coarser pair).mp coarseCapture
    apply (mem_capturePairs_iff catalog finer pair).mpr
    refine ⟨coarseParts.1, ?_⟩
    intro fineAgreement
    exact coarseParts.2 (refines pair.1 pair.2 fineAgreement)
  · intro captureSubset left right fineAgreement
    by_contra coarseSeparation
    have distinct : left ≠ right := by
      intro same
      apply coarseSeparation
      rw [same]
      exact (catalog.theoremAt coarser).primitives.agrees_equivalence.refl right
    have coarseCapture := (mem_capturePairs_iff catalog coarser (left, right)).mpr
      ⟨distinct, coarseSeparation⟩
    exact (mem_capturePairs_iff catalog finer (left, right)).mp
      (captureSubset coarseCapture) |>.2 fineAgreement
theorem kernelRefines_implies_zero_uniqueCapture
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {finer coarser : catalog.Index} (different : finer ≠ coarser)
    (refines : catalog.KernelRefines finer coarser) :
    catalog.uniqueCapturePairs coarser = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair captured
  have parts :=
    (mem_uniqueCapturePairs_iff catalog coarser pair).mp captured
  exact parts.2 finer different
    ((catalog.kernelRefines_iff_capturePairs_subset finer coarser).mp
      refines parts.1)
theorem kernelRefines_implies_zero_uniqueCaptureCount
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {finer coarser : catalog.Index} (different : finer ≠ coarser)
    (refines : catalog.KernelRefines finer coarser) :
    catalog.uniqueCaptureCount coarser = 0 := by
  unfold InformationEscape.Catalog.uniqueCaptureCount
  rw [catalog.kernelRefines_implies_zero_uniqueCapture different refines]
  exact Finset.card_empty
theorem catalogRedundant_iff_exists_zero {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    CatalogRedundant catalog ↔
      ∃ index, catalog.uniqueCaptureCount index = 0 :=
  Iff.rfl
theorem catalogRedundant_iff_not_catalogIrredundant {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    CatalogRedundant catalog ↔ ¬CatalogIrredundant catalog := by
  rw [catalogIrredundant_iff_forall_pos]
  simp only [CatalogRedundant, not_forall, not_lt]
  constructor
  · rintro ⟨index, zero⟩
    exact ⟨index, by omega⟩
  · rintro ⟨index, nonpositive⟩
    exact ⟨index, by omega⟩
theorem catalogIrredundant_iff_redundantIndices_eq_empty {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    CatalogIrredundant catalog ↔ catalog.redundantIndices = ∅ := by
  rw [catalogIrredundant_iff_forall_pos, Finset.eq_empty_iff_forall_notMem]
  simp [redundantIndices]
  exact forall_congr' fun _ => by omega
theorem catalogRedundant_iff_not_irredundant {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    CatalogRedundant catalog ↔ ¬CatalogIrredundant catalog :=
  catalog.catalogRedundant_iff_not_catalogIrredundant
theorem captureSpectrum_sum_eq_denominator {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    (∑ multiplicity, catalog.captureSpectrum multiplicity) =
      (offDiagonalPairs arena.State).card := by
  simpa only [captureSpectrum, Finset.sum_filter, Finset.mem_univ, if_true]
    using (Finset.card_eq_sum_card_fiberwise
      (s := offDiagonalPairs arena.State)
      (t := Finset.univ)
      (f := captureMultiplicityFin catalog)
      (fun _ _ => Finset.mem_univ _)).symm

private theorem captureMultiplicity_eq_zero_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (pair : arena.State × arena.State) :
    catalog.captureMultiplicity pair = 0 ↔
      ∀ index, pair ∉ catalog.capturePairs index := by
  unfold captureMultiplicity
  rw [Finset.card_eq_zero]
  simp
theorem captureSpectrum_zero_eq_fullEscape {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    catalog.captureSpectrum 0 =
      (catalog.escapePairs catalog.fullIndexSet).card := by
  change ((offDiagonalPairs arena.State).filter (fun pair =>
    captureMultiplicityFin catalog pair = 0)).card =
      (catalog.escapePairs catalog.fullIndexSet).card
  apply congrArg Finset.card
  ext pair
  simp only [Finset.mem_filter, Fin.zero_eta, Fin.ext_iff,
    captureMultiplicityFin]
  rw [InformationEscape.Catalog.escapePairs]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨offDiagonal, multiplicityZero⟩
    refine ⟨offDiagonal, (catalog.indistinguishable_iff_forall
      catalog.fullIndexSet pair.1 pair.2).mpr ?_⟩
    intro index _
    by_contra separated
    exact (catalog.captureMultiplicity_eq_zero_iff pair).mp multiplicityZero
      index ((mem_capturePairs_iff catalog index pair).mpr
        ⟨by simpa [offDiagonalPairs] using offDiagonal, separated⟩)
  · rintro ⟨offDiagonal, fullAgreement⟩
    refine ⟨offDiagonal, (catalog.captureMultiplicity_eq_zero_iff pair).mpr ?_⟩
    intro index captured
    exact (mem_capturePairs_iff catalog index pair).mp captured |>.2
      ((catalog.indistinguishable_iff_forall catalog.fullIndexSet
        pair.1 pair.2).mp fullAgreement index (Finset.mem_univ index))

private theorem spectrumOnePairs_eq_uniqueUnion {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) [Nonempty catalog.Index] :
    (offDiagonalPairs arena.State).filter (fun pair =>
        captureMultiplicityFin catalog pair = catalog.captureMultiplicityOne) =
      (Finset.univ : Finset catalog.Index).biUnion fun index =>
        catalog.uniqueCapturePairs index := by
  ext pair
  constructor
  · intro pairMem
    have offDiagonal := (Finset.mem_filter.mp pairMem).1
    have countOne : catalog.captureMultiplicity pair = 1 := by
      have equalFin := (Finset.mem_filter.mp pairMem).2
      simpa [captureMultiplicityFin, captureMultiplicityOne] using
        congrArg Fin.val equalFin
    unfold captureMultiplicity at countOne
    obtain ⟨index, onlyIndex⟩ := Finset.card_eq_one.mp countOne
    apply Finset.mem_biUnion.mpr
    refine ⟨index, Finset.mem_univ index,
      (mem_uniqueCapturePairs_iff catalog index pair).mpr ?_⟩
    have indexCaptured : pair ∈ catalog.capturePairs index := by
      have : index ∈ ((Finset.univ : Finset catalog.Index).filter fun candidate =>
          pair ∈ catalog.capturePairs candidate) := by
        rw [onlyIndex]
        exact Finset.mem_singleton.mpr rfl
      exact (Finset.mem_filter.mp this).2
    refine ⟨indexCaptured, ?_⟩
    intro candidate different candidateCaptured
    have candidateMem : candidate ∈
        ((Finset.univ : Finset catalog.Index).filter fun possible =>
          pair ∈ catalog.capturePairs possible) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ candidate, candidateCaptured⟩
    rw [onlyIndex] at candidateMem
    exact different (Finset.mem_singleton.mp candidateMem)
  · intro pairMem
    obtain ⟨index, _, captured⟩ := Finset.mem_biUnion.mp pairMem
    have parts := (mem_uniqueCapturePairs_iff catalog index pair).mp captured
    apply Finset.mem_filter.mpr
    refine ⟨by simpa [offDiagonalPairs] using
      (mem_capturePairs_iff catalog index pair).mp parts.1 |>.1, ?_⟩
    apply Fin.ext
    simp only [captureMultiplicityFin, captureMultiplicityOne]
    unfold captureMultiplicity
    apply Finset.card_eq_one.mpr
    refine ⟨index, ?_⟩
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro candidateCaptured
      by_contra different
      exact parts.2 candidate different candidateCaptured
    · intro same
      simpa [same] using parts.1
theorem captureSpectrum_one_eq_sum_unique {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) [Nonempty catalog.Index] :
    catalog.captureSpectrum catalog.captureMultiplicityOne =
      ∑ index : catalog.Index, catalog.uniqueCaptureCount index := by
  rw [captureSpectrum]
  rw [catalog.spectrumOnePairs_eq_uniqueUnion]
  have pairwise : ((Finset.univ : Finset catalog.Index) : Set catalog.Index).PairwiseDisjoint
      fun index => catalog.uniqueCapturePairs index := by
    intro left _ right _ different
    exact catalog.uniqueCapturePairs_pairwise_disjoint different
  rw [Finset.card_biUnion pairwise]
  rfl

private theorem spectrum_weighted_sum
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (weight : Nat -> Nat) :
    (∑ multiplicity :
        Fin (@Fintype.card catalog.Index catalog.indexFintype + 1),
      weight multiplicity.1 * catalog.captureSpectrum multiplicity) =
      ∑ pair ∈ offDiagonalPairs arena.State,
        weight (catalog.captureMultiplicity pair) := by
  let fibers := fun multiplicity :
      Fin (@Fintype.card catalog.Index catalog.indexFintype + 1) =>
    (offDiagonalPairs arena.State).filter fun pair =>
      captureMultiplicityFin catalog pair = multiplicity
  calc
    _ = ∑ multiplicity,
        ∑ pair ∈ fibers multiplicity, weight multiplicity.1 := by
      apply Finset.sum_congr rfl
      intro multiplicity _
      rw [Finset.sum_const_nat]
      · rw [Nat.mul_comm]
        rfl
      · intro pair pairMem
        rfl
    _ = ∑ multiplicity ∈ Finset.univ,
        ∑ pair ∈ (offDiagonalPairs arena.State).filter
          (fun pair => captureMultiplicityFin catalog pair = multiplicity),
          weight multiplicity.1 := by rfl
    _ = ∑ multiplicity ∈ Finset.univ,
        ∑ pair ∈ (offDiagonalPairs arena.State).filter
          (fun pair => captureMultiplicityFin catalog pair = multiplicity),
          weight (captureMultiplicityFin catalog pair).1 := by
      apply Finset.sum_congr rfl
      intro multiplicity _
      apply Finset.sum_congr rfl
      intro pair pairMem
      have same := (Finset.mem_filter.mp pairMem).2
      rw [same]
    _ = ∑ pair ∈ offDiagonalPairs arena.State,
        weight (captureMultiplicityFin catalog pair).1 := by
      simpa only [Finset.mem_univ, Finset.filter_true] using
        (Finset.sum_fiberwise_eq_sum_filter
          (s := offDiagonalPairs arena.State)
          (t := (Finset.univ : Finset
            (Fin (@Fintype.card catalog.Index catalog.indexFintype + 1))))
          (g := captureMultiplicityFin catalog)
          (f := fun pair => weight (captureMultiplicityFin catalog pair).1))
    _ = _ := by rfl

private theorem sum_captureMultiplicity_eq_sum_capturePairs_card
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (∑ pair ∈ offDiagonalPairs arena.State,
      catalog.captureMultiplicity pair) =
      ∑ index : catalog.Index, (catalog.capturePairs index).card := by
  simp only [captureMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [← Finset.sum_filter]
  congr 1
  ext pair
  simp only [Finset.mem_filter]
  constructor
  · exact fun parts => parts.2
  · intro captured
    exact ⟨by simpa [offDiagonalPairs] using
      (mem_capturePairs_iff catalog index pair).mp captured |>.1, captured⟩
theorem captureSpectrum_incidence_double_count
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (∑ multiplicity :
        Fin (@Fintype.card catalog.Index catalog.indexFintype + 1),
      multiplicity.1 * catalog.captureSpectrum multiplicity) =
      ∑ index : catalog.Index, (catalog.capturePairs index).card := by
  simpa only [id_eq] using catalog.spectrum_weighted_sum (fun n => n)
    |>.trans catalog.sum_captureMultiplicity_eq_sum_capturePairs_card

private theorem overlapCount_eq_sum_indicator
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (left right : catalog.Index) :
    catalog.pairwiseCaptureOverlapCount left right =
      ∑ pair ∈ offDiagonalPairs arena.State,
        if pair ∈ catalog.capturePairs left ∧
          pair ∈ catalog.capturePairs right then 1 else 0 := by
  unfold pairwiseCaptureOverlapCount pairwiseCaptureOverlapPairs
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  congr 1
  ext pair
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨leftCaptured, rightCaptured⟩
    exact ⟨by simpa [offDiagonalPairs] using
      (mem_capturePairs_iff catalog left pair).mp leftCaptured |>.1,
      leftCaptured, rightCaptured⟩
  · rintro ⟨_, leftCaptured, rightCaptured⟩
    exact ⟨leftCaptured, rightCaptured⟩

private theorem orderedOverlap_eq_pair_factorialSum
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    catalog.orderedDistinctOverlapTotal =
      ∑ pair ∈ offDiagonalPairs arena.State,
        catalog.captureMultiplicity pair *
          (catalog.captureMultiplicity pair - 1) := by
  unfold orderedDistinctOverlapTotal
  simp_rw [catalog.overlapCount_eq_sum_indicator]
  calc
    (∑ left : catalog.Index,
        ∑ right ∈ (Finset.univ : Finset catalog.Index).erase left,
          ∑ pair ∈ offDiagonalPairs arena.State,
            if pair ∈ catalog.capturePairs left ∧
              pair ∈ catalog.capturePairs right then 1 else 0) =
      ∑ left : catalog.Index,
        ∑ pair ∈ offDiagonalPairs arena.State,
          ∑ right ∈ (Finset.univ : Finset catalog.Index).erase left,
            if pair ∈ catalog.capturePairs left ∧
              pair ∈ catalog.capturePairs right then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro left _
        rw [Finset.sum_comm]
    _ = ∑ pair ∈ offDiagonalPairs arena.State,
        ∑ left : catalog.Index,
          ∑ right ∈ (Finset.univ : Finset catalog.Index).erase left,
            if pair ∈ catalog.capturePairs left ∧
              pair ∈ catalog.capturePairs right then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ pair ∈ offDiagonalPairs arena.State,
        catalog.captureMultiplicity pair *
          (catalog.captureMultiplicity pair - 1) := by
      apply Finset.sum_congr rfl
      intro pair _
      let captured := (Finset.univ : Finset catalog.Index).filter fun index =>
        pair ∈ catalog.capturePairs index
      have cardCaptured : captured.card = catalog.captureMultiplicity pair := by
        rfl
      calc
        (∑ left : catalog.Index,
            ∑ right ∈ (Finset.univ : Finset catalog.Index).erase left,
              if pair ∈ catalog.capturePairs left ∧
                pair ∈ catalog.capturePairs right then 1 else 0) =
          ∑ left : catalog.Index,
            if left ∈ captured then captured.card - 1 else 0 := by
          apply Finset.sum_congr rfl
          intro left _
          by_cases leftCaptured : left ∈ captured
          · have pairCaptured : pair ∈ catalog.capturePairs left :=
              (Finset.mem_filter.mp leftCaptured).2
            rw [Finset.sum_boole]
            have filteredEq :
                ((Finset.univ.erase left).filter fun right =>
                  pair ∈ catalog.capturePairs left ∧
                    pair ∈ catalog.capturePairs right) =
                  captured.erase left := by
              ext right
              simp [captured, pairCaptured, and_assoc]
            rw [filteredEq, Finset.card_erase_of_mem leftCaptured]
            simp [leftCaptured]
          · have pairNotCaptured : pair ∉ catalog.capturePairs left := by
              simpa [captured] using leftCaptured
            simp [pairNotCaptured, leftCaptured]
        _ = captured.card * (captured.card - 1) := by
          rw [← Finset.sum_filter]
          simp [captured, Finset.sum_const_nat]
        _ = catalog.captureMultiplicity pair *
            (catalog.captureMultiplicity pair - 1) := by
          rw [cardCaptured]
theorem pairwiseOverlap_spectrum_doubleCount
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    catalog.orderedDistinctOverlapTotal =
      catalog.captureSpectrumSecondFactorialMoment := by
  rw [catalog.orderedOverlap_eq_pair_factorialSum]
  unfold captureSpectrumSecondFactorialMoment
  rw [catalog.spectrum_weighted_sum (fun multiplicity =>
    multiplicity * (multiplicity - 1))]
theorem catalogRoleHistogram_sum {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) [Nonempty catalog.Index] :
    (∑ signature with signature ≠ fun _ => false,
      catalog.roleHistogramTotal signature) =
      ∑ index : catalog.Index, catalog.uniqueCaptureCount index ∧
    (∑ index : catalog.Index, catalog.uniqueCaptureCount index) =
      catalog.captureSpectrum catalog.captureMultiplicityOne := by
  constructor
  · unfold roleHistogramTotal
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro index _
    exact catalog.roleHistogram_sum_eq_uniqueCaptureCount index
  · exact (catalog.captureSpectrum_one_eq_sum_unique).symm
theorem spectrum_total {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    (∑ multiplicity, catalog.captureSpectrum multiplicity) =
      (offDiagonalPairs arena.State).card :=
  catalog.captureSpectrum_sum_eq_denominator
theorem spectrum_zero {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    catalog.captureSpectrum 0 =
      (catalog.escapePairs catalog.fullIndexSet).card :=
  catalog.captureSpectrum_zero_eq_fullEscape
theorem spectrum_unique {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) [Nonempty catalog.Index] :
    catalog.captureSpectrum catalog.captureMultiplicityOne =
      ∑ index : catalog.Index, catalog.uniqueCaptureCount index :=
  catalog.captureSpectrum_one_eq_sum_unique
theorem spectrum_first_moment {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    (∑ multiplicity :
        Fin (@Fintype.card catalog.Index catalog.indexFintype + 1),
      multiplicity.1 * catalog.captureSpectrum multiplicity) =
      ∑ index : catalog.Index, (catalog.capturePairs index).card :=
  catalog.captureSpectrum_incidence_double_count
theorem spectrum_second_moment {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) :
    catalog.captureSpectrumSecondFactorialMoment =
      catalog.orderedDistinctOverlapTotal :=
  catalog.pairwiseOverlap_spectrum_doubleCount.symm
theorem overlap_symmetric_diagonal {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    catalog.pairwiseCaptureOverlapPairs left right =
        catalog.pairwiseCaptureOverlapPairs right left ∧
      catalog.pairwiseCaptureOverlapPairs left left =
        catalog.capturePairs left :=
  ⟨catalog.pairwiseCaptureOverlap_comm left right,
    catalog.pairwiseCaptureOverlap_diag left⟩
theorem refinement_overlap {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index)
    (refines : catalog.KernelRefines finer coarser) :
    catalog.capturePairs coarser ⊆ catalog.capturePairs finer ∧
      catalog.pairwiseCaptureOverlapPairs finer coarser =
        catalog.capturePairs coarser := by
  have subset :=
    (catalog.kernelRefines_iff_capturePairs_subset finer coarser).mp refines
  refine ⟨subset, ?_⟩
  unfold pairwiseCaptureOverlapPairs
  exact Finset.inter_eq_right.mpr subset

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
