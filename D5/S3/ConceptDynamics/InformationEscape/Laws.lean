/- GID: D5/S3/ConceptDynamics/InformationEscape/Laws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/Laws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Catalog escape is invariant under index and kernel equivalence. -/

import D5.S3.ConceptDynamics.InformationEscape.ExactRate

/- Library-search audit trail (2026-09-04):
   * Repository searches for catalog reindexing, unique-capture congruence,
     irredundant catalogs, and augmented statements found no existing owners.
   * Exact current-tree hits `PrimitiveBundle.agrees_congr_of_kernel_eq`,
     `Catalog.lowersEscape_iff_uniqueCaptureCount_pos`, and
     `Catalog.mem_without_iff` are reused directly.
   * Pinned Mathlib supplies `Fintype.ofEquiv`, `Equiv.decidableEq`, finite
     decidability of universal propositions, and Finset extensionality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w z

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

/-- Transport a catalog along an equivalence of its finite index type. -/
def reindex {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {J : Type z} (equivalence : catalog.Index ≃ J) : Catalog.{u, v, z} arena where
  Index := J
  indexFintype := by
    letI := catalog.indexFintype
    exact Fintype.ofEquiv catalog.Index equivalence
  indexDecidableEq := by
    letI := catalog.indexDecidableEq
    exact equivalence.symm.decidableEq
  theoremAt index := catalog.theoremAt (equivalence.symm index)

/-- Retain a catalog's finite index carrier while replacing its theorem family. -/
def withTheoremAt {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena) : Catalog.{u, z, w} arena where
  Index := catalog.Index
  indexFintype := catalog.indexFintype
  indexDecidableEq := catalog.indexDecidableEq
  theoremAt := units

/-- IE-015: relabelling indices preserves escape for every selected subset. -/
theorem escapePairs_reindex
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {J : Type z} (equivalence : catalog.Index ≃ J)
    (selected : Finset catalog.Index) :
    (catalog.reindex equivalence).escapePairs
        (selected.map equivalence.toEmbedding) =
      catalog.escapePairs selected := by
  apply Finset.ext
  intro pair
  simp only [escapePairs, Finset.mem_filter]
  apply and_congr Iff.rfl
  constructor
  · intro agreement
    apply (catalog.indistinguishable_iff_forall selected pair.1 pair.2).2
    intro candidate candidateMem
    have transportedMem : equivalence candidate ∈
        selected.map equivalence.toEmbedding :=
      Finset.mem_map.2 ⟨candidate, candidateMem, rfl⟩
    simpa [reindex] using (Catalog.indistinguishable_iff_forall
      (catalog.reindex equivalence) (selected.map equivalence.toEmbedding)
      pair.1 pair.2).1 agreement (equivalence candidate) transportedMem
  · intro agreement
    apply (Catalog.indistinguishable_iff_forall
      (catalog.reindex equivalence) (selected.map equivalence.toEmbedding)
      pair.1 pair.2).2
    intro candidate candidateMem
    obtain ⟨original, originalMem, rfl⟩ := Finset.mem_map.1 candidateMem
    change (catalog.theoremAt (equivalence.symm (equivalence original))).primitives.agrees
      pair.1 pair.2
    simpa using
      (catalog.indistinguishable_iff_forall selected pair.1 pair.2).1
        agreement original originalMem

/-- IE-015: relabelling indices preserves the exact escape rate of every subset. -/
theorem escapeRate_reindex
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {J : Type z} (equivalence : catalog.Index ≃ J)
    (selected : Finset catalog.Index) :
    (catalog.reindex equivalence).escapeRate
        (selected.map equivalence.toEmbedding) =
      catalog.escapeRate selected := by
  unfold escapeRate escapeNumerator
  rw [catalog.escapePairs_reindex equivalence selected]

private theorem uniqueCapturePairs_reindex
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {J : Type z} (equivalence : catalog.Index ≃ J) (index : catalog.Index) :
    (catalog.reindex equivalence).uniqueCapturePairs (equivalence index) =
      catalog.uniqueCapturePairs index := by
  apply Finset.ext
  intro pair
  have indistinguishableEq :
      (catalog.reindex equivalence).indistinguishable
          ((catalog.reindex equivalence).without (equivalence index))
          pair.1 pair.2 ↔
        catalog.indistinguishable (catalog.without index) pair.1 pair.2 := by
    constructor
    · intro agreement
      apply (catalog.indistinguishable_iff_forall
        (catalog.without index) pair.1 pair.2).2
      intro candidate candidateMem
      have transportedMem : equivalence candidate ∈
          (catalog.reindex equivalence).without (equivalence index) := by
        apply ((catalog.reindex equivalence).mem_without_iff
          (equivalence index) (equivalence candidate)).2
        intro same
        exact ((catalog.mem_without_iff index candidate).1 candidateMem)
          (equivalence.injective same)
      simpa [reindex] using (Catalog.indistinguishable_iff_forall
        (catalog.reindex equivalence)
        ((catalog.reindex equivalence).without (equivalence index))
        pair.1 pair.2).1 agreement (equivalence candidate)
          transportedMem
    · intro agreement
      apply (Catalog.indistinguishable_iff_forall
        (catalog.reindex equivalence)
        ((catalog.reindex equivalence).without (equivalence index))
        pair.1 pair.2).2
      intro candidate candidateMem
      have preimageNe : equivalence.symm candidate ≠ index := by
        intro same
        have candidateEq : candidate = equivalence index := by
          apply equivalence.symm.injective
          simpa using same
        exact ((catalog.reindex equivalence).mem_without_iff
          (equivalence index) candidate).1 candidateMem candidateEq
      simpa [reindex] using (catalog.indistinguishable_iff_forall
        (catalog.without index) pair.1 pair.2).1 agreement
          (equivalence.symm candidate)
          ((catalog.mem_without_iff index (equivalence.symm candidate)).2 preimageNe)
  have escapeEq :
      pair ∈ (catalog.reindex equivalence).escapePairs
          ((catalog.reindex equivalence).without (equivalence index)) ↔
        pair ∈ catalog.escapePairs (catalog.without index) := by
    simp only [escapePairs, Finset.mem_filter]
    exact and_congr Iff.rfl indistinguishableEq
  simp only [uniqueCapturePairs, Finset.mem_filter]
  rw [escapeEq]
  simp [reindex]

/-- IE-015: relabelling the finite theorem indices preserves unique capture. -/
theorem uniqueCaptureCount_reindex
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {J : Type z} (equivalence : catalog.Index ≃ J) (index : catalog.Index) :
    (catalog.reindex equivalence).uniqueCaptureCount (equivalence index) =
      catalog.uniqueCaptureCount index := by
  unfold uniqueCaptureCount
  rw [uniqueCapturePairs_reindex]

/-- IE-015: relabelling theorem indices preserves the corresponding exact gain rate. -/
theorem theoremGainRate_reindex
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {J : Type z} (equivalence : catalog.Index ≃ J) (index : catalog.Index) :
    (catalog.reindex equivalence).theoremGainRate (equivalence index) =
      catalog.theoremGainRate index := by
  unfold theoremGainRate
  rw [catalog.uniqueCaptureCount_reindex equivalence index]

private theorem uniqueCapturePairs_congr_agrees
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameAgreement : ∀ index left right,
      (catalog.theoremAt index).primitives.agrees left right ↔
        (units index).primitives.agrees left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).uniqueCapturePairs index =
      catalog.uniqueCapturePairs index := by
  apply Finset.ext
  intro pair
  have withoutEq :
      (catalog.withTheoremAt units).without index = catalog.without index := rfl
  have indistinguishableEq :
      (catalog.withTheoremAt units).indistinguishable
          ((catalog.withTheoremAt units).without index) pair.1 pair.2 ↔
        catalog.indistinguishable (catalog.without index) pair.1 pair.2 := by
    constructor
    · intro agreement
      apply (catalog.indistinguishable_iff_forall
        (catalog.without index) pair.1 pair.2).2
      intro candidate candidateMem
      apply (sameAgreement candidate pair.1 pair.2).2
      have transportedMem : candidate ∈
          (catalog.withTheoremAt units).without index := by
        rw [withoutEq]
        exact candidateMem
      exact (Catalog.indistinguishable_iff_forall
        (catalog.withTheoremAt units)
        ((catalog.withTheoremAt units).without index)
        pair.1 pair.2).1 agreement candidate transportedMem
    · intro agreement
      apply (Catalog.indistinguishable_iff_forall
        (catalog.withTheoremAt units)
        ((catalog.withTheoremAt units).without index)
        pair.1 pair.2).2
      intro candidate candidateMem
      apply (sameAgreement candidate pair.1 pair.2).1
      have originalMem : candidate ∈ catalog.without index := by
        rw [← withoutEq]
        exact candidateMem
      exact (catalog.indistinguishable_iff_forall
        (catalog.without index) pair.1 pair.2).1 agreement candidate
          originalMem
  have escapeEq :
      pair ∈ (catalog.withTheoremAt units).escapePairs
          ((catalog.withTheoremAt units).without index) ↔
        pair ∈ catalog.escapePairs (catalog.without index) := by
    simp only [escapePairs, Finset.mem_filter]
    exact and_congr Iff.rfl indistinguishableEq
  simp only [uniqueCapturePairs, Finset.mem_filter]
  rw [escapeEq]
  simpa only [withTheoremAt] using
    and_congr Iff.rfl (not_congr (sameAgreement index pair.1 pair.2).symm)

/-- IE-016 / CIRPT-IE-016: pointwise equality of theorem bundle kernels preserves
every unique-capture finset. -/
theorem uniqueCapturePairs_congr_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ index left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (units index).primitives.toKernel.relation left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).uniqueCapturePairs index =
      catalog.uniqueCapturePairs index := by
  have sameAgreement : ∀ candidate left right,
      (catalog.theoremAt candidate).primitives.agrees left right ↔
        (units candidate).primitives.agrees left right := by
    intro candidate
    exact (PrimitiveBundle.agrees_congr_of_kernel_eq
      (catalog.theoremAt candidate).primitives
      (units candidate).primitives (sameKernel candidate)).1
  exact catalog.uniqueCapturePairs_congr_agrees units sameAgreement index

/-- IE-016 / CIRPT-IE-016: kernel-equivalent theorem families preserve every
unique-capture count. -/
theorem uniqueCaptureCount_congr_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ index left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (units index).primitives.toKernel.relation left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).uniqueCaptureCount index =
      catalog.uniqueCaptureCount index := by
  unfold uniqueCaptureCount
  rw [catalog.uniqueCapturePairs_congr_kernel units sameKernel index]

/-- CIRPT-IE-016: kernel-equivalent theorem families preserve full-catalog
escape pairs. -/
theorem escapePairs_congr_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ index left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (units index).primitives.toKernel.relation left right) :
    (catalog.withTheoremAt units).escapePairs
        (catalog.withTheoremAt units).fullIndexSet =
      catalog.escapePairs catalog.fullIndexSet := by
  have sameAgreement : ∀ candidate left right,
      (catalog.theoremAt candidate).primitives.agrees left right ↔
        (units candidate).primitives.agrees left right := by
    intro candidate
    exact (PrimitiveBundle.agrees_congr_of_kernel_eq
      (catalog.theoremAt candidate).primitives
      (units candidate).primitives (sameKernel candidate)).1
  apply Finset.ext
  intro pair
  simp only [escapePairs, Finset.mem_filter]
  apply and_congr Iff.rfl
  constructor
  · intro agreement
    apply (catalog.indistinguishable_iff_forall
      catalog.fullIndexSet pair.1 pair.2).2
    intro candidate _
    apply (sameAgreement candidate pair.1 pair.2).2
    exact (Catalog.indistinguishable_iff_forall
      (catalog.withTheoremAt units)
      (catalog.withTheoremAt units).fullIndexSet pair.1 pair.2).1
        agreement candidate (Finset.mem_univ candidate)
  · intro agreement
    apply (Catalog.indistinguishable_iff_forall
      (catalog.withTheoremAt units)
      (catalog.withTheoremAt units).fullIndexSet pair.1 pair.2).2
    intro candidate _
    apply (sameAgreement candidate pair.1 pair.2).1
    exact (catalog.indistinguishable_iff_forall
      catalog.fullIndexSet pair.1 pair.2).1 agreement candidate
        (Finset.mem_univ candidate)

/-- CIRPT-IE-016: kernel-equivalent theorem families preserve the full-catalog
escape count. -/
theorem escapeCount_congr_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ index left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (units index).primitives.toKernel.relation left right) :
    ((catalog.withTheoremAt units).escapePairs
        (catalog.withTheoremAt units).fullIndexSet).card =
      (catalog.escapePairs catalog.fullIndexSet).card := by
  rw [catalog.escapePairs_congr_kernel units sameKernel]

/-- CIRPT-IE-016: kernel-equivalent theorem families preserve the full-catalog
escape rate. -/
theorem escapeRate_congr_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ index left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (units index).primitives.toKernel.relation left right) :
    (catalog.withTheoremAt units).escapeRate
        (catalog.withTheoremAt units).fullIndexSet =
      catalog.escapeRate catalog.fullIndexSet := by
  unfold escapeRate escapeNumerator
  rw [catalog.escapePairs_congr_kernel units sameKernel]

/-- Primitive-realization corollary of kernel invariance for a replacement family. -/
theorem uniqueCaptureCount_congr_primitiveRealization
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (replaced : catalog.Index)
    {firstSig : PrimitiveSignature.{u, v, z} arena.State}
    {secondSig : PrimitiveSignature.{u, v, z} arena.State}
    (first : PrimitiveRealization firstSig)
    (second : PrimitiveRealization secondSig)
    (sameAgreement : ∀ left right,
      first.toPrimitiveBundle.agrees left right ↔
        second.toPrimitiveBundle.agrees left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt (fun candidate =>
      if candidate = replaced then
        { primitives := first.toPrimitiveBundle
          Statement := (catalog.theoremAt candidate).Statement
          proof := (catalog.theoremAt candidate).proof }
      else catalog.theoremAt candidate)).uniqueCaptureCount index =
    (catalog.withTheoremAt (fun candidate =>
      if candidate = replaced then
        { primitives := second.toPrimitiveBundle
          Statement := (catalog.theoremAt candidate).Statement
          proof := (catalog.theoremAt candidate).proof }
      else catalog.theoremAt candidate)).uniqueCaptureCount index := by
  let firstUnits := fun candidate =>
    if candidate = replaced then
      { primitives := first.toPrimitiveBundle
        Statement := (catalog.theoremAt candidate).Statement
        proof := (catalog.theoremAt candidate).proof }
    else catalog.theoremAt candidate
  let secondUnits := fun candidate =>
    if candidate = replaced then
      { primitives := second.toPrimitiveBundle
        Statement := (catalog.theoremAt candidate).Statement
        proof := (catalog.theoremAt candidate).proof }
    else catalog.theoremAt candidate
  have kernels : ∀ candidate left right,
      (firstUnits candidate).primitives.toKernel.relation left right ↔
        (secondUnits candidate).primitives.toKernel.relation left right := by
    intro candidate left right
    by_cases same : candidate = replaced
    · simpa [firstUnits, secondUnits, same, PrimitiveBundle.toKernel] using
        sameAgreement left right
    · simp [firstUnits, secondUnits, same]
  exact (uniqueCaptureCount_congr_kernel
    (catalog.withTheoremAt firstUnits) secondUnits kernels index).symm

end Catalog

/-- IE-017: every catalog theorem lowers escape when removed. -/
def CatalogIrredundant {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) : Prop :=
  ∀ index, catalog.LowersEscape index

/-- IE-017: irredundancy is exactly positivity of every unique-capture count. -/
theorem catalogIrredundant_iff_forall_pos
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    CatalogIrredundant catalog ↔
      ∀ index, 0 < catalog.uniqueCaptureCount index := by
  by_cases nondegenerate : arena.Nondegenerate
  · unfold CatalogIrredundant
    apply forall_congr'
    intro index
    exact catalog.lowersEscape_iff_uniqueCaptureCount_pos index nondegenerate
  · have denominatorZero : escapeDenominator arena = 0 := by
      rw [escapeDenominator_eq]
      unfold Arena.Nondegenerate at nondegenerate
      have cardCases : arena.card = 0 ∨ arena.card = 1 := by omega
      rcases cardCases with cardZero | cardOne
      · simp [cardZero]
      · simp [cardOne]
    unfold CatalogIrredundant
    apply forall_congr'
    intro index
    have uniqueZero : catalog.uniqueCaptureCount index = 0 := by
      have pairsEmpty : offDiagonalPairs arena.State = ∅ := by
        apply Finset.card_eq_zero.mp
        exact denominatorZero
      simp [Catalog.uniqueCaptureCount, Catalog.uniqueCapturePairs,
        Catalog.escapePairs, pairsEmpty]
    rw [uniqueZero]
    simp [Catalog.LowersEscape, Catalog.escapeRate, denominatorZero]

/-- Irredundancy is decidable by finite exact unique-capture counts. -/
instance catalogIrredundantDecidable
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    Decidable (CatalogIrredundant catalog) := by
  letI := catalog.indexFintype
  exact decidable_of_iff (∀ index, 0 < catalog.uniqueCaptureCount index)
    (catalogIrredundant_iff_forall_pos catalog).symm

/-- IE-022: the original theorem statement paired with its positive escape contribution. -/
def AugmentedStatement {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  (catalog.theoremAt index).Statement ∧ catalog.LowersEscape index

/-- IE-022: enrich a theorem proof with a proof of its escape contribution. -/
theorem augmentedProof {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (gain : catalog.LowersEscape index) :
    AugmentedStatement catalog index :=
  ⟨(catalog.theoremAt index).proof, gain⟩

/-- IE-023: an irredundant catalog supplies an augmented proof for every unit. -/
theorem catalog_all_augmented
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    CatalogIrredundant catalog → ∀ index, AugmentedStatement catalog index := by
  intro irredundant index
  exact augmentedProof catalog index (irredundant index)

private abbrev decidabilityFixtureArena : Arena := Arena.ofFintype Bool

private abbrev separatingFixtureBundle : PrimitiveBundle Bool where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel id⟩

private abbrev collapsedFixtureBundle : PrimitiveBundle Bool where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel (fun _ => true)⟩

private abbrev decidabilityFixtureUnit (bundle : PrimitiveBundle Bool) :
    TheoremUnit decidabilityFixtureArena where
  primitives := bundle
  Statement := True
  proof := trivial

private abbrev separatingCatalog : Catalog decidabilityFixtureArena :=
  Catalog.ofVector fun _ : Fin 1 => decidabilityFixtureUnit separatingFixtureBundle

private abbrev collapsedCatalog : Catalog decidabilityFixtureArena :=
  Catalog.ofVector fun _ : Fin 1 => decidabilityFixtureUnit collapsedFixtureBundle

/- The public instance kernel-reduces on the vector-backed seal shape. -/
example : CatalogIrredundant separatingCatalog := by decide

example : ¬CatalogIrredundant collapsedCatalog := by decide

end D5.S3.ConceptDynamics.InformationEscape
