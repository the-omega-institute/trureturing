/- GID: D5/S3/ConceptDynamics/InformationEscape/Laws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/Laws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Catalog gains are invariant under reindexing and kernel-equivalent primitive presentations. -/

import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty

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
every unique-capture count. -/
theorem uniqueCaptureCount_congr_kernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (units : catalog.Index -> TheoremUnit.{u, z} arena)
    (sameKernel : ∀ index left right,
      (catalog.theoremAt index).primitives.toKernel.relation left right ↔
        (units index).primitives.toKernel.relation left right)
    (index : catalog.Index) :
    (catalog.withTheoremAt units).uniqueCaptureCount index =
      catalog.uniqueCaptureCount index := by
  have sameAgreement : ∀ candidate left right,
      (catalog.theoremAt candidate).primitives.agrees left right ↔
        (units candidate).primitives.agrees left right := by
    intro candidate
    exact (PrimitiveBundle.agrees_congr_of_kernel_eq
      (catalog.theoremAt candidate).primitives
      (units candidate).primitives (sameKernel candidate)).1
  unfold uniqueCaptureCount
  rw [catalog.uniqueCapturePairs_congr_agrees units sameAgreement index]

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
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (nondegenerate : arena.Nondegenerate) :
    CatalogIrredundant catalog ↔
      ∀ index, 0 < catalog.uniqueCaptureCount index := by
  unfold CatalogIrredundant
  apply forall_congr'
  intro index
  exact catalog.lowersEscape_iff_uniqueCaptureCount_pos index nondegenerate

/-- Irredundancy is decidable by finite exact unique-capture counts. -/
instance catalogIrredundantDecidable
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    Decidable (CatalogIrredundant catalog) := by
  letI := catalog.indexFintype
  unfold CatalogIrredundant Catalog.LowersEscape
  infer_instance

/-- IE-022: the original theorem statement paired with its positive escape contribution. -/
def AugmentedStatement {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  (catalog.theoremAt index).Statement ∧ catalog.LowersEscape index

/-- IE-022: enrich a theorem proof with a proof of its escape contribution. -/
def augmentedProof {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (gain : catalog.LowersEscape index) :
    AugmentedStatement catalog index :=
  ⟨(catalog.theoremAt index).proof, gain⟩

/-- IE-023: an irredundant catalog supplies an augmented proof for every unit. -/
theorem catalog_all_augmented
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    CatalogIrredundant catalog → ∀ index, AugmentedStatement catalog index := by
  intro irredundant index
  exact augmentedProof catalog index (irredundant index)

end D5.S3.ConceptDynamics.InformationEscape
