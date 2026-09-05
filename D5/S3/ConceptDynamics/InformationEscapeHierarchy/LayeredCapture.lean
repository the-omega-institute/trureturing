/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certified kernel chains partition finite arenas into captures and unresolved pairs. -/

import D5.S3.ConceptDynamics.InformationEscapeHierarchy.KernelChain
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.AnalysisLaws
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.SDiff
import Mathlib.Order.Fin.Basic

/- Library-search audit trail (2026-09-05):
   * Repository searches for `LayerChain`, `layeredCapture`, catalog occurrences,
     maximal catalogs, redundant indices, and system-wide positivity found no
     existing owner. Exact current-tree hits `CatalogIrredundant`,
     `Catalog.uniqueCapturePairs`, `Catalog.kernelRefines_implies_zero_uniqueCapture`,
     `GeneratorSchedule.increment`, and `Catalog.GeneratedKernel.edgeCapture`
     are reused below.
   * Pinned Mathlib exact hits `Fin.antitone_iff_succ_le`,
     `Finset.sdiff_nonempty`, `Finset.sdiff_union_of_subset`, and finite-set
     disjointness provide the chain partition and strictness algebra.
   * No repository or pinned-Mathlib declaration packages a dependently typed
     finite family of catalogs or the ordered initial/successor layer convention. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT
open Lean

universe u v w z

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

/-- A stable name for one catalog projection. -/
structure CatalogId where
  name : Name
  deriving DecidableEq, Repr

/-- Whether a catalog is the canonical maximal family or a bounded analysis view. -/
inductive CatalogKind
  | canonicalMaximal
  | analysisView
  deriving DecidableEq, Repr

/-- One theorem occurrence together with its root, catalog, arena, and realization identity. -/
structure CatalogOccurrence (arena : Arena.{u}) where
  rootId : Name
  catalogId : CatalogId
  catalogKind : CatalogKind
  objectArenaName : Name
  theoremName : Name
  unitName : Name
  realizationName : Name
  unit : TheoremUnit.{u, v} arena

/-- Assemble the canonical catalog at one root and object arena from its occurrence closure. -/
def maximalCatalog {arena : Arena.{u}} (rootId objectArenaName : Name)
    (occurrences : Array (CatalogOccurrence.{u, v} arena)) : Catalog.{u, v, 0} arena := by
  let members := occurrences.filter fun occurrence =>
    occurrence.rootId == rootId &&
      occurrence.objectArenaName == objectArenaName &&
      occurrence.catalogKind == .canonicalMaximal
  exact
    { Index := Fin members.size
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      theoremAt := fun index => members[index].unit }

/-- A finite sequence of kernels with a certified refinement at every adjacency. -/
structure LayerChain (arena : Arena.{u}) where
  length : Nat
  kernel : Fin (length + 1) -> DecidableKernel arena.State
  refines : forall r : Fin length,
    (kernel r.succ).relation <= (kernel r.castSucc).relation

namespace LayerChain

private def survivingPairs {arena : Arena.{u}} (chain : LayerChain arena)
    (position : Fin (chain.length + 1)) : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (offDiagonalPairs arena.State).filter fun pair =>
    (chain.kernel position).relation pair.1 pair.2

private def stagePairs {arena : Arena.{u}} (chain : LayerChain arena) :
    Fin (chain.length + 2) -> Finset (arena.State × arena.State) :=
  Fin.cases (offDiagonalPairs arena.State) chain.survivingPairs

/-- Pairs first captured at a layer; layer zero precedes the first listed kernel. -/
def layeredCapturePairs {arena : Arena.{u}} (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) : Finset (arena.State × arena.State) :=
  chain.stagePairs layer.castSucc \ chain.stagePairs layer.succ

/-- Number of pairs first captured at one layer. -/
def layeredCaptureCount {arena : Arena.{u}} (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) : Nat :=
  (chain.layeredCapturePairs layer).card

/-- The ordered vector of all layered capture counts. -/
def layeredCaptureSpectrum {arena : Arena.{u}} (chain : LayerChain arena) :
    Fin (chain.length + 1) -> Nat :=
  chain.layeredCaptureCount

/-- Exact fraction of all off-diagonal pairs captured at one layer. -/
def layeredCaptureRate {arena : Arena.{u}} (chain : LayerChain arena)
    (layer : Fin (chain.length + 1)) : Rat :=
  (chain.layeredCaptureCount layer : Rat) / (escapeDenominator arena : Rat)

/-- Pairs still unresolved by the finest listed kernel. -/
def unresolvedPairs {arena : Arena.{u}} (chain : LayerChain arena) :
    Finset (arena.State × arena.State) :=
  chain.survivingPairs ⟨chain.length, Nat.lt_succ_self chain.length⟩

/-- Number of pairs still unresolved by the finest listed kernel. -/
def unresolvedCount {arena : Arena.{u}} (chain : LayerChain arena) : Nat :=
  chain.unresolvedPairs.card

/-- Exact unresolved fraction at the finest listed kernel. -/
def unresolvedRate {arena : Arena.{u}} (chain : LayerChain arena) : Rat :=
  (chain.unresolvedCount : Rat) / (escapeDenominator arena : Rat)

private theorem stage_succ_subset {arena : Arena.{u}} (chain : LayerChain arena)
    (r : Fin (chain.length + 1)) :
    chain.stagePairs r.succ ⊆ chain.stagePairs r.castSucc := by
  refine Fin.cases ?_ (fun position => ?_) r
  · intro pair membership
    exact (Finset.mem_filter.mp membership).1
  · intro pair membership
    have parts := Finset.mem_filter.mp membership
    apply Finset.mem_filter.mpr
    refine ⟨parts.1, ?_⟩
    exact chain.refines position pair.1 pair.2 parts.2

private theorem stage_antitone {arena : Arena.{u}} (chain : LayerChain arena) :
    Antitone chain.stagePairs :=
  Fin.antitone_iff_succ_le.mpr chain.stage_succ_subset

private theorem exists_membership_boundary
    {alpha : Type u} {n : Nat} (sets : Fin (n + 1) -> Finset alpha)
    (element : alpha)
    (atStart : element ∈ sets 0)
    (notAtEnd : element ∉ sets ⟨n, Nat.lt_succ_self n⟩) :
    ∃ r : Fin n, element ∈ sets r.castSucc ∧ element ∉ sets r.succ := by
  induction n with
  | zero =>
      exfalso
      exact notAtEnd (by simpa using atStart)
  | succ n inductionHypothesis =>
      by_cases atNext : element ∈ sets (Fin.succ 0)
      · let tailSets : Fin (n + 1) -> Finset alpha := fun r => sets r.succ
        have tailNotAtEnd : element ∉ tailSets ⟨n, Nat.lt_succ_self n⟩ := by
          change element ∉ sets (Fin.succ ⟨n, Nat.lt_succ_self n⟩)
          rw [show (Fin.succ ⟨n, Nat.lt_succ_self n⟩ : Fin (n + 2)) =
              ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ by
            apply Fin.ext
            rfl]
          exact notAtEnd
        obtain ⟨r, atLeft, notAtRight⟩ :=
          inductionHypothesis tailSets atNext tailNotAtEnd
        refine ⟨r.succ, ?_, ?_⟩
        · change element ∈ sets r.castSucc.succ at atLeft
          rw [show r.succ.castSucc = r.castSucc.succ by apply Fin.ext; rfl]
          exact atLeft
        · exact notAtRight
      · exact ⟨0, by simpa using atStart, by simpa using atNext⟩

private theorem layeredCapture_union {arena : Arena.{u}} (chain : LayerChain arena) :
    Finset.univ.biUnion chain.layeredCapturePairs =
      chain.stagePairs 0 \
        chain.stagePairs ⟨chain.length + 1, Nat.lt_succ_self (chain.length + 1)⟩ := by
  ext pair
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    layeredCapturePairs, Finset.mem_sdiff]
  constructor
  · rintro ⟨r, inLayer⟩
    refine ⟨chain.stage_antitone (Fin.zero_le r.castSucc) inLayer.1, ?_⟩
    intro atEnd
    exact inLayer.2
      (chain.stage_antitone (Fin.le_last r.succ) atEnd)
  · rintro ⟨atStart, notAtEnd⟩
    obtain ⟨r, atLeft, notAtRight⟩ :=
      exists_membership_boundary chain.stagePairs pair atStart notAtEnd
    exact ⟨r, atLeft, notAtRight⟩

private theorem layeredCapture_disjoint_of_lt
    {arena : Arena.{u}} (chain : LayerChain arena)
    {r s : Fin (chain.length + 1)} (less : r < s) :
    Disjoint (chain.layeredCapturePairs r) (chain.layeredCapturePairs s) := by
  apply Finset.disjoint_left.mpr
  intro pair inFirst inSecond
  have firstParts := Finset.mem_sdiff.mp inFirst
  have secondParts := Finset.mem_sdiff.mp inSecond
  apply firstParts.2
  apply chain.stage_antitone
    (show r.succ <= s.castSucc by simpa using less)
  exact secondParts.1

private theorem layeredCapture_disjoint_unresolved
    {arena : Arena.{u}} (chain : LayerChain arena)
    (r : Fin (chain.length + 1)) :
    Disjoint (chain.layeredCapturePairs r) chain.unresolvedPairs := by
  apply Finset.disjoint_left.mpr
  intro pair inLayer unresolved
  have layerParts := Finset.mem_sdiff.mp inLayer
  apply layerParts.2
  apply chain.stage_antitone (Fin.le_last r.succ)
  exact unresolved

/-- The initial layer is nonempty exactly when the first kernel separates a pair. -/
theorem layeredCapture_zero_nonempty_iff
    {arena : Arena.{u}} (chain : LayerChain arena) :
    (chain.layeredCapturePairs ⟨0, Nat.zero_lt_succ _⟩).Nonempty ↔
      ∃ x y, x ≠ y ∧
        ¬(chain.kernel ⟨0, Nat.zero_lt_succ _⟩).relation x y := by
  constructor
  · rintro ⟨pair, membership⟩
    have parts := Finset.mem_sdiff.mp membership
    have distinct := (Finset.mem_filter.mp parts.1).2
    refine ⟨pair.1, pair.2, distinct, ?_⟩
    intro related
    apply parts.2
    exact Finset.mem_filter.mpr ⟨parts.1, related⟩
  · rintro ⟨x, y, distinct, separated⟩
    refine ⟨(x, y), Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · simp [stagePairs, offDiagonalPairs, distinct]
    · intro inFirstKernel
      exact separated (Finset.mem_filter.mp inFirstKernel).2

/-- A successor layer is nonempty exactly when the next kernel removes a related pair. -/
theorem layeredCapture_succ_nonempty_iff_strict
    {arena : Arena.{u}} (chain : LayerChain arena) (r : Fin chain.length) :
    (chain.layeredCapturePairs r.succ).Nonempty ↔
      ∃ x y,
        (chain.kernel r.castSucc).relation x y ∧
          ¬(chain.kernel r.succ).relation x y := by
  constructor
  · rintro ⟨pair, membership⟩
    have parts := Finset.mem_sdiff.mp membership
    refine ⟨pair.1, pair.2, (Finset.mem_filter.mp parts.1).2, ?_⟩
    intro related
    exact parts.2 (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp parts.1).1, related⟩)
  · rintro ⟨x, y, related, separated⟩
    have distinct : x ≠ y := by
      intro same
      subst y
      exact separated ((chain.kernel r.succ).equivalence.refl x)
    refine ⟨(x, y), Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr
        ⟨by simp [offDiagonalPairs, distinct], related⟩
    · intro inNext
      exact separated (Finset.mem_filter.mp inNext).2

/-- IE-036: the ordered layers and final unresolved set form a disjoint partition. -/
theorem layeredCapture_partition
    {arena : Arena.{u}} (chain : LayerChain arena) :
    (∀ r s : Fin (chain.length + 1), r ≠ s ->
      Disjoint (chain.layeredCapturePairs r) (chain.layeredCapturePairs s)) ∧
    (∀ r : Fin (chain.length + 1),
      Disjoint (chain.layeredCapturePairs r) chain.unresolvedPairs) ∧
    Finset.univ.biUnion chain.layeredCapturePairs ∪ chain.unresolvedPairs =
      offDiagonalPairs arena.State := by
  constructor
  · intro r s different
    rcases lt_or_gt_of_ne different with less | greater
    · exact chain.layeredCapture_disjoint_of_lt less
    · exact (chain.layeredCapture_disjoint_of_lt greater).symm
  constructor
  · exact chain.layeredCapture_disjoint_unresolved
  · rw [chain.layeredCapture_union]
    apply Finset.sdiff_union_of_subset
    exact chain.stage_antitone (Fin.zero_le _)

/-- IE-037: strict adjacent refinement is exactly nonempty successor capture. -/
theorem strictRefinement_iff_layeredCapture_nonempty
    {arena : Arena.{u}} (chain : LayerChain arena) (r : Fin chain.length) :
    ((chain.kernel r.succ).relation <= (chain.kernel r.castSucc).relation ∧
      ¬(chain.kernel r.castSucc).relation <= (chain.kernel r.succ).relation) ↔
      (chain.layeredCapturePairs r.succ).Nonempty := by
  rw [chain.layeredCapture_succ_nonempty_iff_strict]
  constructor
  · rintro ⟨_, notReverse⟩
    by_contra noWitness
    apply notReverse
    intro x y related
    by_contra separated
    exact noWitness ⟨x, y, related, separated⟩
  · rintro ⟨x, y, related, separated⟩
    refine ⟨chain.refines r, ?_⟩
    intro reverse
    exact separated (reverse x y related)

end LayerChain

namespace Catalog

/-- IE-038: a distinct finer peer makes a coarser flat member uniquely capture nothing. -/
theorem cumulativeChain_coarser_uniqueCapture_zero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {finer coarser : catalog.Index}
    (different : finer ≠ coarser)
    (refines : catalog.KernelRefines finer coarser) :
    catalog.uniqueCapturePairs coarser = ∅ :=
  catalog.kernelRefines_implies_zero_uniqueCapture different refines

end Catalog

/-- One dependent arena/catalog pair. -/
structure PackedCatalog where
  arena : Arena.{u}
  catalog : Catalog.{u, v, w} arena

/-- The finite maximal-catalog family owned by one designated sealing root. -/
structure DesignatedRootCatalogSuite where
  rootId : Name
  CatalogIndex : Type z
  catalogIndexFintype : Fintype CatalogIndex
  catalogIndexDecidableEq : DecidableEq CatalogIndex
  catalogAt : CatalogIndex -> PackedCatalog.{u, v, w}

/-- Every maximal catalog in a designated root has positive unique capture at every member. -/
def SystemCatalogIrredundant (suite : DesignatedRootCatalogSuite.{u, v, w, z}) : Prop :=
  ∀ index, CatalogIrredundant (suite.catalogAt index).catalog

/-- Compatibility name for the same single-root universal catalog verdict. -/
abbrev SystemWidePositive (suite : DesignatedRootCatalogSuite.{u, v, w, z}) : Prop :=
  SystemCatalogIrredundant suite

/-- IE-039: system-wide positivity is exactly designated-root catalog irredundancy. -/
theorem systemWidePositive_iff_systemCatalogIrredundant
    (suite : DesignatedRootCatalogSuite.{u, v, w, z}) :
    SystemWidePositive suite ↔ SystemCatalogIrredundant suite :=
  Iff.rfl

private def Catalog.GeneratedKernel.toDecidableKernel
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : DecidableKernel arena.State where
  relation := node.relation
  equivalence := by
    induction node using Quotient.inductionOn with
    | _ selected => exact catalog.indistinguishable_equivalence selected
  decidableRelation := node.relationDecidable

namespace GeneratorSchedule

/-- Regard every generated schedule node as a kernel in a certified general layer chain. -/
def toLayerChain {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) : LayerChain arena where
  length := schedule.length
  kernel := fun position => (schedule.node position).toDecidableKernel
  refines := by
    intro r
    cases schedule.classification r with
    | strict proof =>
        exact proof.1.choose_spec.2.2
    | collapsed same proof =>
        rw [same]

/-- Generated LayerChain successor captures are exactly GeneratorSchedule increments. -/
theorem toLayerChain_layeredCapture_succ_eq_increment
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (r : Fin schedule.length) :
    schedule.toLayerChain.layeredCapturePairs r.succ = schedule.increment r := by
  rfl

end GeneratorSchedule

end D5.S3.ConceptDynamics.InformationEscape
