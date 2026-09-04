/- GID: D5/S3/ConceptDynamics/InformationEscape/RoleHistogram
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/RoleHistogram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero residual role signatures partition exactly one theorem's unique capture pairs. -/

import D5.S3.ConceptDynamics.InformationEscape.Laws

/- Library-search audit trail (2026-09-04):
   * Repository searches found the exact reusable CIRPT declarations
     `PrimitiveBundle.residualSignatureHistogram`,
     `mem_kernelResidual_iff_residualRoleSignature_ne_zero`, and
     `Finset.sum_card_fiberwise_eq_card_filter` usage in `RoleSignature`.
   * `Catalog.indistinguishable_equivalence` packages the leave-one-out
     catalog relation; no existing catalog-level residual histogram was found.
   * Pinned Mathlib's fiberwise cardinality theorem is reused directly; no
     finite partition counting lemma is reproved here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w z

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

/-- The decidable joint kernel of every theorem except the specified unit. -/
def withoutKernel {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : DecidableKernel arena.State where
  relation := catalog.indistinguishable (catalog.without index)
  equivalence := catalog.indistinguishable_equivalence (catalog.without index)
  decidableRelation := fun left right =>
    catalog.indistinguishableDecidable (catalog.without index) left right

/-- CIRPT-IE-015: unique capture is the residual of the other theorem kernels
against the selected theorem's primitive kernel. -/
theorem uniqueCapturePairs_eq_kernelResidual
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    (catalog.uniqueCapturePairs index : Set (arena.State × arena.State)) =
      kernelResidual (catalog.withoutKernel index)
        (catalog.theoremAt index).primitives.toKernel := by
  ext pair
  change pair ∈ catalog.uniqueCapturePairs index ↔
    catalog.indistinguishable (catalog.without index) pair.1 pair.2 ∧
      ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2
  constructor
  · intro captured
    have uniqueParts := Finset.mem_filter.mp captured
    have escapeParts := Finset.mem_filter.mp uniqueParts.1
    exact ⟨escapeParts.2, uniqueParts.2⟩
  · rintro ⟨otherAgreement, selectedSeparation⟩
    have distinct : pair.1 ≠ pair.2 := by
      intro same
      apply selectedSeparation
      rw [same]
      exact (catalog.theoremAt index).primitives.agrees_equivalence.refl pair.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, otherAgreement⟩, selectedSeparation⟩
    simpa [offDiagonalPairs] using distinct

/-- Multiplicity of one four-role signature relative to a unit's leave-one-out kernel. -/
def roleHistogram {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (signature : Fin 4 -> Bool) : Nat :=
  (catalog.theoremAt index).primitives.residualSignatureHistogram
    (catalog.withoutKernel index) signature

/-- CIRPT-IE-017: every uniquely captured pair has a nonzero residual role signature. -/
theorem uniqueCapture_roleSignature_nonzero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (pair : arena.State × arena.State)
    (captured : pair ∈ catalog.uniqueCapturePairs index) :
    (catalog.theoremAt index).primitives.residualRoleSignature
        (catalog.withoutKernel index) pair.1 pair.2 ≠ fun _ => false := by
  apply (PrimitiveBundle.mem_kernelResidual_iff_residualRoleSignature_ne_zero
    (catalog.withoutKernel index) (catalog.theoremAt index).primitives pair).1
  rw [← catalog.uniqueCapturePairs_eq_kernelResidual index]
  exact captured

/-- CIRPT-IE-017: unique capture is the union of its four active-role fibers. -/
theorem uniqueCapturePairs_eq_biUnion_roleFibers
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.uniqueCapturePairs index =
      Finset.univ.biUnion fun coordinate : Fin 4 =>
        (catalog.uniqueCapturePairs index).filter fun pair =>
          (catalog.theoremAt index).primitives.residualRoleSignature
            (catalog.withoutKernel index) pair.1 pair.2 coordinate = true := by
  classical
  apply Finset.ext
  intro pair
  constructor
  · intro captured
    have nonzero := catalog.uniqueCapture_roleSignature_nonzero index pair captured
    have existsActive : ∃ coordinate,
        (catalog.theoremAt index).primitives.residualRoleSignature
          (catalog.withoutKernel index) pair.1 pair.2 coordinate = true := by
      by_contra noneActive
      apply nonzero
      funext coordinate
      apply Bool.eq_false_of_not_eq_true
      intro active
      exact noneActive ⟨coordinate, active⟩
    obtain ⟨coordinate, active⟩ := existsActive
    apply Finset.mem_biUnion.mpr
    exact ⟨coordinate, Finset.mem_univ coordinate,
      Finset.mem_filter.mpr ⟨captured, active⟩⟩
  · intro covered
    obtain ⟨coordinate, _, pairMem⟩ := Finset.mem_biUnion.mp covered
    exact (Finset.mem_filter.mp pairMem).1

/-- The nonzero role-signature buckets sum to the theorem's exact unique-capture count. -/
theorem roleHistogram_sum_eq_uniqueCaptureCount
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    ∑ signature with signature ≠ fun _ => false,
        catalog.roleHistogram index signature =
      catalog.uniqueCaptureCount index := by
  classical
  let bundle := (catalog.theoremAt index).primitives
  let current := catalog.withoutKernel index
  have histogramSum :
      ∑ signature with signature ≠ fun _ => false,
          bundle.residualSignatureHistogram current signature =
        ((offDiagonalPairs arena.State).filter fun pair =>
          bundle.residualRoleSignature current pair.1 pair.2 ≠
            fun _ => false).card := by
    simpa only [PrimitiveBundle.residualSignatureHistogram,
      Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (offDiagonalPairs arena.State)
        (Finset.univ.filter fun signature : Fin 4 -> Bool =>
          signature ≠ fun _ => false)
        (fun pair => bundle.residualRoleSignature current pair.1 pair.2))
  have capturedPairs :
      (offDiagonalPairs arena.State).filter (fun pair =>
          bundle.residualRoleSignature current pair.1 pair.2 ≠
            fun _ => false) =
        catalog.uniqueCapturePairs index := by
    apply Finset.ext
    intro pair
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨offDiagonal, nonzero⟩
      have residual :=
        (PrimitiveBundle.mem_kernelResidual_iff_residualRoleSignature_ne_zero
          current bundle pair).2 nonzero
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨offDiagonal, residual.1⟩, residual.2⟩
    · intro captured
      have uniqueParts := Finset.mem_filter.mp captured
      have escapeParts := Finset.mem_filter.mp uniqueParts.1
      exact ⟨escapeParts.1,
        catalog.uniqueCapture_roleSignature_nonzero index pair captured⟩
  unfold roleHistogram uniqueCaptureCount
  simpa [bundle, current, capturedPairs] using histogramSum

/-- CIRPT-IE-018: exact theorem gain depends only on the pointwise family of
primitive agreement kernels. -/
theorem theoremGain_depends_only_on_primitive_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ candidate left right,
      (catalog.theoremAt candidate).primitives.toKernel.relation left right ↔
        (units candidate).primitives.toKernel.relation left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).theoremGainRate index =
      catalog.theoremGainRate index := by
  unfold theoremGainRate
  rw [catalog.uniqueCaptureCount_congr_kernel units sameKernel index]

/-- CIRPT-IE-021: a theorem unit carrying only the closed-truth kernel has no
unique object-level capture. -/
theorem closed_truth_uniqueCaptureCount_zero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index)
    (closedTruthKernel : ∀ left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (cutKernel (fun _ : arena.State => true)).relation left right) :
    catalog.uniqueCaptureCount index = 0 := by
  unfold uniqueCaptureCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair captured
  have separated := (Finset.mem_filter.mp captured).2
  exact separated (closedTruthKernel pair.1 pair.2 |>.2 rfl)

/-- CIRPT-IE-019: theorem statements and proof certificates do not affect
unique capture when every object-level primitive bundle is unchanged. -/
theorem theoremAt_proof_irrelevant
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, v} arena)
    (samePrimitives : ∀ candidate,
      (catalog.theoremAt candidate).primitives = (units candidate).primitives)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).uniqueCaptureCount index =
      catalog.uniqueCaptureCount index := by
  apply catalog.uniqueCaptureCount_congr_kernel units
  intro candidate left right
  rw [samePrimitives candidate]

end Catalog

/-- CIRPT-IE-021: the constant closed-truth readout has the universal kernel. -/
theorem closed_truth_cut_kernel_universal (X : Type u) :
    (cutKernel (fun _ : X => true)).relation = fun _ _ => True := by
  funext left right
  simp [cutKernel]

private abbrev histogramFixtureArena : Arena :=
  Arena.ofFintype (Bool × Bool)

private abbrev histogramFirstBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.fst⟩

private abbrev histogramSecondBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.snd⟩

private abbrev histogramUnit (bundle : PrimitiveBundle (Bool × Bool)) :
    TheoremUnit histogramFixtureArena where
  primitives := bundle
  Statement := True
  proof := trivial

private def histogramFixtureCatalog : Catalog histogramFixtureArena where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt
    | false => histogramUnit histogramFirstBundle
    | true => histogramUnit histogramSecondBundle

/- Kernel-reduced fixture: nonzero role buckets count the four ordered pairs
uniquely separated by the first-coordinate CUT. -/
example :
    ∑ signature with signature ≠ fun _ => false,
        histogramFixtureCatalog.roleHistogram false signature = 4 := by
  decide

end D5.S3.ConceptDynamics.InformationEscape
