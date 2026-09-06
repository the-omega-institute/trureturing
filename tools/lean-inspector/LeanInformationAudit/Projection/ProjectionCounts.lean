import LeanInformationAudit.Projection.ProjectionKernel

namespace LeanInformationAudit

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

def projectionOverlapCount {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (left right : catalog.Index) : Nat :=
  ((offDiagonalPairs arena.State).filter fun pair =>
    ¬(catalog.theoremAt left).primitives.agrees pair.1 pair.2 ∧
    ¬(catalog.theoremAt right).primitives.agrees pair.1 pair.2).card

theorem projectionOverlapCount_eq {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (left right : catalog.Index) :
    projectionOverlapCount catalog left right = catalog.pairwiseCaptureOverlapCount left right := by
  apply congrArg Finset.card
  ext pair
  simp [Catalog.pairwiseCaptureOverlapPairs,
    Catalog.capturePairs, Catalog.escapePairs, Catalog.indistinguishable_iff_forall]
  tauto

def projectionMultiplicity {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (pair : arena.State × arena.State) : Nat :=
  (Finset.univ.filter fun index =>
    ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2).card

theorem projectionMultiplicity_eq {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (pair : arena.State × arena.State) (member : pair ∈ offDiagonalPairs arena.State) :
    projectionMultiplicity catalog pair = catalog.captureMultiplicity pair := by
  apply congrArg Finset.card
  ext index
  simp [Catalog.capturePairs, Catalog.escapePairs,
    Catalog.indistinguishable_iff_forall, member]

def projectionSpectrum {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : Fin (Fintype.card catalog.Index + 1)) : Nat :=
  ((offDiagonalPairs arena.State).filter fun pair =>
    projectionMultiplicity catalog pair = index.val).card

theorem projectionSpectrum_eq {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : Fin (Fintype.card catalog.Index + 1)) :
    projectionSpectrum catalog index = catalog.captureSpectrum index := by
  apply congrArg Finset.card
  ext pair
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro member
  rw [projectionMultiplicity_eq catalog pair member]
  constructor
  · intro equal
    apply Fin.ext
    exact equal
  · intro equal
    exact congrArg Fin.val equal

theorem projectionEdgeCount_eq {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (source target : catalog.GeneratedKernel) (refines : target ≤ source) :
    source.edgeCaptureCount target = source.escapeCount - target.escapeCount := by
  apply Finset.card_sdiff_of_subset
  intro pair member
  simp only [Catalog.GeneratedKernel.escapeAt, Finset.mem_filter] at member ⊢
  exact ⟨member.1, refines _ _ member.2⟩

theorem projectionIncrementCount_eq {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (index : Fin schedule.length) :
    schedule.incrementCount index = (schedule.node index.castSucc).escapeCount -
      (schedule.node index.succ).escapeCount :=
  projectionEdgeCount_eq _ _ (schedule.toLayerChain.refines index)

theorem projectionLeaveOneOut_eq {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (node : catalog.GeneratedKernel)
    (same : catalog.generatedKernel (catalog.without index) = node) :
    node.edgeCapture (catalog.generatedKernel catalog.fullIndexSet) =
      catalog.uniqueCapturePairs index := by
  subst node
  exact (catalog.uniqueCapturePairs_eq_sdiff index).symm

theorem projectionInitialLayerCount_eq {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) :
    schedule.toLayerChain.layeredCaptureCount 0 = 0 := by
  change ((offDiagonalPairs arena.State) \ (schedule.node 0).escapeAt).card = 0
  rw [schedule.starts_at_top]
  apply Finset.card_eq_zero.mpr
  apply Finset.sdiff_eq_empty_iff_subset.mpr
  intro pair member
  change pair ∈ (offDiagonalPairs arena.State).filter
    (fun pair => catalog.indistinguishable ∅ pair.1 pair.2)
  simp [member, Catalog.indistinguishable_iff_forall]

theorem projectionSuccessorLayerCount_eq {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (index : Fin schedule.length) :
    schedule.toLayerChain.layeredCaptureCount index.succ = schedule.incrementCount index := rfl

theorem projectionSingletonSystemRedundant {arena : Arena.{u}}
    (root : Lean.Name) (original normalized : Catalog.{u, v, w} arena)
    (same : normalized = original) (index : normalized.Index)
    (zero : normalized.uniqueCaptureCount index = 0) :
    ¬SystemCatalogIrredundant (projectionSuite root ![PackedCatalog.mk arena original]) := by
  subst original
  intro positive
  have nonzero := (catalogIrredundant_iff_forall_pos normalized).mp
    (positive (0 : Fin 1)) index
  omega

end LeanInformationAudit
