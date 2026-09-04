/- GID: D5/S3/ConceptDynamics/InformationEscape/ExactRate
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ExactRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite escape counts yield exact rational rates and positive unique-capture criteria. -/

import D5.S3.ConceptDynamics.InformationEscape.EscapePairs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order

/- Library-search audit trail (2026-09-04):
   * Repository searches for `escapeDenominator`, `escapeRate`,
     `uniqueCaptureCount`, and leave-one-out rate laws found no existing
     declarations under `D5`.
   * Exact current-tree hits `Catalog.escapePairs_without_eq_union` and
     `escapePairs_full_disjoint_uniqueCapturePairs` supply the additive
     leave-one-out count without reconstructing its finite-set proof.
   * Pinned Mathlib exact hits `Finset.card_eq_sum_card_fiberwise`,
     `Finset.card_bij`, `Finset.card_erase_of_mem`,
     `Finset.card_union_of_disjoint`, `Finset.card_pos`,
     `div_lt_div_iff_of_pos_right`, and `Nat.cast_pos` supply all counting
     and rational-order steps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

/-- The number of ordered pairs of distinct arena states. -/
def escapeDenominator (arena : Arena.{u}) : Nat := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact (offDiagonalPairs arena.State).card

/-- The escape denominator is the ordered-pair count `card * (card - 1)`. -/
theorem escapeDenominator_eq (arena : Arena.{u}) :
    escapeDenominator arena = arena.card * (arena.card - 1) := by
  let pairs := offDiagonalPairs arena.State
  have fiberCard (left : arena.State) :
      (pairs.filter fun pair => pair.1 = left).card =
        (Finset.univ.erase left : Finset arena.State).card := by
    apply Finset.card_bij (fun pair _ => pair.2)
    · intro pair pairInFiber
      have pairInOffDiagonal := (Finset.mem_filter.mp pairInFiber).1
      have firstEq := (Finset.mem_filter.mp pairInFiber).2
      have distinct : pair.1 ≠ pair.2 := by
        simpa [pairs, offDiagonalPairs] using pairInOffDiagonal
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro secondEq
      exact distinct (firstEq.trans secondEq.symm)
    · intro first firstMem second secondMem secondEq
      apply Prod.ext
      · exact (Finset.mem_filter.mp firstMem).2.trans
          (Finset.mem_filter.mp secondMem).2.symm
      · exact secondEq
    · intro right rightInErase
      have rightNe : right ≠ left := (Finset.mem_erase.mp rightInErase).1
      refine ⟨(left, right), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      simp [pairs, offDiagonalPairs, rightNe.symm]
  have firstCoordinateMapsTo :
      (pairs : Set (arena.State × arena.State)).MapsTo Prod.fst
        (Finset.univ : Finset arena.State) := by
    intro pair _
    exact Finset.mem_univ pair.1
  calc
    escapeDenominator arena = pairs.card := rfl
    _ = ∑ left ∈ (Finset.univ : Finset arena.State),
        (pairs.filter fun pair => pair.1 = left).card :=
      Finset.card_eq_sum_card_fiberwise firstCoordinateMapsTo
    _ = ∑ _left ∈ (Finset.univ : Finset arena.State), (arena.card - 1) := by
      simp_rw [fiberCard, Finset.card_erase_of_mem (Finset.mem_univ _)]
      rfl
    _ = arena.card * (arena.card - 1) := by
      simp [Arena.card]

/-- A nondegenerate arena has at least one ordered off-diagonal pair. -/
theorem escapeDenominator_pos (arena : Arena.{u}) (nondegenerate : arena.Nondegenerate) :
    0 < escapeDenominator arena := by
  obtain ⟨left, right, distinct⟩ := arena.exists_ne_of_nondegenerate nondegenerate
  apply Finset.card_pos.mpr
  exact ⟨(left, right), by simp [offDiagonalPairs, distinct]⟩

namespace Catalog

/-- The number of ordered distinct pairs left indistinguishable by a selection. -/
def escapeNumerator {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) : Nat :=
  (catalog.escapePairs selected).card

/-- The exact escape fraction of a selected finite catalog. -/
def escapeRate {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) : Rat :=
  (catalog.escapeNumerator selected : Rat) / (escapeDenominator arena : Rat)

/-- The number of ordered pairs uniquely captured by one theorem. -/
def uniqueCaptureCount {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Nat :=
  (catalog.uniqueCapturePairs index).card

/-- The exact fraction of all off-diagonal pairs uniquely captured by one theorem. -/
def theoremGainRate {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Rat :=
  (catalog.uniqueCaptureCount index : Rat) / (escapeDenominator arena : Rat)

/-- Removing a theorem strictly raises the exact escape rate. -/
def LowersEscape {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  catalog.escapeRate catalog.fullIndexSet < catalog.escapeRate (catalog.without index)

/-- IE-007: leave-one-out escape count is persistent escape plus unique capture. -/
theorem escapeNumerator_without_eq
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.escapeNumerator (catalog.without index) =
      catalog.escapeNumerator catalog.fullIndexSet +
        catalog.uniqueCaptureCount index := by
  unfold escapeNumerator uniqueCaptureCount
  rw [catalog.escapePairs_without_eq_union index]
  exact Finset.card_union_of_disjoint
    (catalog.escapePairs_full_disjoint_uniqueCapturePairs index)

/-- IE-008: the leave-one-out rate increase is exactly the theorem gain rate. -/
theorem theoremGainRate_eq
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.escapeRate (catalog.without index) -
        catalog.escapeRate catalog.fullIndexSet =
      catalog.theoremGainRate index := by
  have denominatorPositive : (0 : Rat) < escapeDenominator arena :=
    Nat.cast_pos.mpr (escapeDenominator_pos arena nondegenerate)
  have denominatorNonzero : (escapeDenominator arena : Rat) ≠ 0 :=
    ne_of_gt denominatorPositive
  unfold escapeRate theoremGainRate
  rw [div_sub_div_same]
  apply (div_left_inj' denominatorNonzero).2
  rw [catalog.escapeNumerator_without_eq index, Nat.cast_add]
  simp

/-- The exact rate criterion reduces to a positive natural unique-capture count. -/
theorem lowersEscape_iff_uniqueCaptureCount_pos
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.LowersEscape index ↔ 0 < catalog.uniqueCaptureCount index := by
  have denominatorPositive : (0 : Rat) < escapeDenominator arena :=
    Nat.cast_pos.mpr (escapeDenominator_pos arena nondegenerate)
  unfold LowersEscape escapeRate
  rw [div_lt_div_iff_of_pos_right denominatorPositive]
  norm_cast
  rw [catalog.escapeNumerator_without_eq index]
  simp

/-- IE-009: a positive unique-capture count is equivalent to a concrete pair witness. -/
theorem uniqueCaptureCount_pos_iff_witness
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    0 < catalog.uniqueCaptureCount index ↔
      ∃ left right, left ≠ right ∧
        (∀ candidate, candidate ≠ index ->
          (catalog.theoremAt candidate).primitives.agrees left right) ∧
        ¬(catalog.theoremAt index).primitives.agrees left right := by
  rw [uniqueCaptureCount, Finset.card_pos]
  constructor
  · rintro ⟨⟨left, right⟩, pairMembership⟩
    have uniqueParts := Finset.mem_filter.mp pairMembership
    have escapeParts := Finset.mem_filter.mp uniqueParts.1
    have distinct : left ≠ right := by
      simpa [offDiagonalPairs] using escapeParts.1
    refine ⟨left, right, distinct, ?_, uniqueParts.2⟩
    intro candidate candidateNe
    exact escapeParts.2 candidate
      ((catalog.mem_without_iff index candidate).mpr candidateNe)
  · rintro ⟨left, right, distinct, otherAgreement, indexSeparation⟩
    refine ⟨(left, right), Finset.mem_filter.mpr ⟨?_, indexSeparation⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simp [offDiagonalPairs, distinct]
    · intro candidate candidateInWithout
      exact otherAgreement candidate
        ((catalog.mem_without_iff index candidate).mp candidateInWithout)

end Catalog

private abbrev exactRateFixtureArena : Arena :=
  Arena.ofFintype (Bool × Bool)

private abbrev exactRateFirstBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.fst⟩

private abbrev exactRateSecondBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.snd⟩

private abbrev exactRateFirstUnit : TheoremUnit exactRateFixtureArena where
  primitives := exactRateFirstBundle
  Statement := True
  proof := True.intro

private abbrev exactRateSecondUnit : TheoremUnit exactRateFixtureArena where
  primitives := exactRateSecondBundle
  Statement := True
  proof := True.intro

private def exactRateFixtureCatalog : Catalog exactRateFixtureArena where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt
    | false => exactRateFirstUnit
    | true => exactRateSecondUnit

/- Each coordinate uniquely captures four ordered pairs. -/
example : exactRateFixtureCatalog.uniqueCaptureCount false = 4 := by
  decide

example : exactRateFixtureCatalog.uniqueCaptureCount true = 4 := by
  decide

end D5.S3.ConceptDynamics.InformationEscape
