/- GID: D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/StructuralNovelty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Escape reduction is strict kernel novelty outside the canonical semantic closure. -/

import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion

/- Library-search audit trail (2026-09-04):
   * Repository searches for `StructurallyLowersEscape`,
     `semanticClosureWithout`, finite catalog novelty, recoverable kernels, and
     same-kernel zero capture found no existing declarations under `D5`.
   * Exact current-tree hits `Catalog.jointKernel_antitone`,
     `Catalog.uniqueCaptureCount_pos_iff_witness`, and
     `Catalog.lowersEscape_iff_uniqueCaptureCount_pos` supply the finite
     structural/counting equivalences.
   * Exact canonical hit
     `StrictKernelNoveltyCriterion.strict_kernel_novelty_criterion` is applied
     to tagged quotient CUTs. The sigma output makes the heterogeneous catalog
     bundles a homogeneous `Set (Concept X Output)` without erasing their
     object-level kernels.
   * Pinned Mathlib exact hits `Set.ssubset_iff_exists` and
     `mem_semanticClosure_iff_fiber_constant` supply strictness witnesses and
     the canonical semantic-closure characterization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion

universe u v w

namespace Catalog

/-- Strict shrinkage from the leave-one-out kernel to the full catalog kernel. -/
def StructurallyLowersEscape
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  catalog.jointKernel Set.univ ⊂
    catalog.jointKernel {candidate | candidate ≠ index}

private theorem structurallyLowersEscape_iff_witness
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.StructurallyLowersEscape index ↔
      ∃ left right, left ≠ right ∧
        (∀ candidate, candidate ≠ index ->
          (catalog.theoremAt candidate).primitives.agrees left right) ∧
        ¬(catalog.theoremAt index).primitives.agrees left right := by
  constructor
  · intro strict
    rcases (Set.ssubset_iff_exists.mp strict).2 with
      ⟨pair, pairInWithout, pairNotInFull⟩
    have indexSeparation :
        ¬(catalog.theoremAt index).primitives.agrees pair.1 pair.2 := by
      intro indexAgreement
      apply pairNotInFull
      intro candidate _
      by_cases same : candidate = index
      · subst candidate
        exact indexAgreement
      · exact pairInWithout candidate same
    have distinct : pair.1 ≠ pair.2 := by
      intro same
      apply indexSeparation
      rw [same]
      exact (catalog.theoremAt index).primitives.agrees_equivalence.refl pair.2
    exact ⟨pair.1, pair.2, distinct,
      fun candidate candidateNe => pairInWithout candidate candidateNe,
      indexSeparation⟩
  · rintro ⟨left, right, _distinct, otherAgreement, indexSeparation⟩
    apply Set.ssubset_iff_exists.mpr
    refine ⟨catalog.jointKernel_antitone (Set.subset_univ _), ?_⟩
    refine ⟨(left, right), ?_, ?_⟩
    · intro candidate candidateNe
      exact otherAgreement candidate candidateNe
    · intro pairInFull
      exact indexSeparation (pairInFull index (Set.mem_univ index))

/-- IE-010: finite rate reduction and strict Set-level kernel shrinkage agree. -/
theorem structurallyLowersEscape_iff_lowersEscape
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.StructurallyLowersEscape index ↔ catalog.LowersEscape index := by
  rw [catalog.structurallyLowersEscape_iff_witness index]
  rw [catalog.lowersEscape_iff_uniqueCaptureCount_pos index nondegenerate]
  exact (catalog.uniqueCaptureCount_pos_iff_witness index).symm

/-- Kernels implied by every leave-one-out catalog agreement. -/
def semanticClosureWithout
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Set (DecidableKernel arena.State) :=
  {candidate | ∀ left right,
    (∀ other, other ≠ index ->
      (catalog.theoremAt other).primitives.agrees left right) ->
    candidate.relation left right}

/-- One common codomain containing every catalog bundle's canonical quotient. -/
def QuotientOutput
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) : Type (max u w) :=
  Sigma fun index : catalog.Index =>
    Quotient (catalog.theoremAt index).primitives.toKernel.toSetoid

/-- The index-tagged canonical quotient CUT of a theorem bundle. -/
def taggedQuotientCut
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Concept arena.State catalog.QuotientOutput :=
  fun state =>
    ⟨index, (catalog.theoremAt index).primitives.toKernel.quotientCut state⟩

/-- The homogeneous family of tagged quotient CUTs excluding one theorem. -/
def quotientCutsWithout
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    Set (Concept arena.State catalog.QuotientOutput) :=
  catalog.taggedQuotientCut '' {other | other ≠ index}

private theorem taggedQuotientCut_eq_iff_agrees
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (left right : arena.State) :
    catalog.taggedQuotientCut index left =
        catalog.taggedQuotientCut index right ↔
      (catalog.theoremAt index).primitives.agrees left right := by
  change
    ((⟨index,
        (catalog.theoremAt index).primitives.toKernel.quotientCut left⟩ :
          catalog.QuotientOutput) =
      (⟨index,
        (catalog.theoremAt index).primitives.toKernel.quotientCut right⟩ :
          catalog.QuotientOutput)) ↔ _
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  exact (quotient_cut_kernel_normal_form
    (catalog.theoremAt index).primitives.toKernel left right).symm

/-- The catalog closure is the canonical semantic closure of tagged quotient CUTs. -/
theorem taggedQuotientCut_mem_semanticClosure_iff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.taggedQuotientCut index ∈
        SemanticClosure (catalog.quotientCutsWithout index) ↔
      (catalog.theoremAt index).primitives.toKernel ∈
        catalog.semanticClosureWithout index := by
  rw [mem_semanticClosure_iff_fiber_constant]
  constructor
  · intro canonicalInvariant left right otherAgreement
    apply (catalog.taggedQuotientCut_eq_iff_agrees index left right).1
    apply canonicalInvariant
    intro definition
    rcases definition.2 with ⟨other, otherNe, definitionEq⟩
    rw [← definitionEq]
    apply (catalog.taggedQuotientCut_eq_iff_agrees other left right).2
    exact otherAgreement other otherNe
  · intro catalogInvariant left right allTaggedEqual
    apply (catalog.taggedQuotientCut_eq_iff_agrees index left right).2
    apply catalogInvariant left right
    intro other otherNe
    apply (catalog.taggedQuotientCut_eq_iff_agrees other left right).1
    exact allTaggedEqual
      ⟨catalog.taggedQuotientCut other, ⟨other, otherNe, rfl⟩⟩

private theorem lowersEscape_iff_not_mem_semanticClosureWithout_direct
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.LowersEscape index ↔
      (catalog.theoremAt index).primitives.toKernel ∉
        catalog.semanticClosureWithout index := by
  rw [catalog.lowersEscape_iff_uniqueCaptureCount_pos index nondegenerate]
  rw [catalog.uniqueCaptureCount_pos_iff_witness index]
  constructor
  · rintro ⟨left, right, _distinct, otherAgreement, indexSeparation⟩ invariant
    exact indexSeparation (invariant left right otherAgreement)
  · intro outside
    by_contra noWitness
    apply outside
    intro left right otherAgreement
    by_contra indexSeparation
    change ¬(catalog.theoremAt index).primitives.agrees left right at indexSeparation
    apply noWitness
    refine ⟨left, right, ?_, otherAgreement, indexSeparation⟩
    intro same
    subst right
    have reflexive :=
      (catalog.theoremAt index).primitives.agrees_equivalence.refl left
    exact indexSeparation reflexive

/-- The rate criterion is an instance of the canonical strict-kernel novelty theorem. -/
theorem lowersEscape_iff_strict_kernel_novelty
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.LowersEscape index ↔
      D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointKernel
          (fun definition : Set.insert (catalog.taggedQuotientCut index)
              (catalog.quotientCutsWithout index) => definition.1) ⊂
        D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointKernel
          (fun definition : catalog.quotientCutsWithout index => definition.1) := by
  rw [strict_kernel_novelty_criterion]
  exact (catalog.lowersEscape_iff_not_mem_semanticClosureWithout_direct
    index nondegenerate).trans
      (not_congr (catalog.taggedQuotientCut_mem_semanticClosure_iff index).symm)

/-- IE-011: lowering escape is failure of leave-one-out semantic recoverability. -/
theorem lowersEscape_iff_not_mem_semanticClosureWithout
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.LowersEscape index ↔
      (catalog.theoremAt index).primitives.toKernel ∉
        catalog.semanticClosureWithout index := by
  rw [catalog.lowersEscape_iff_strict_kernel_novelty index nondegenerate]
  rw [strict_kernel_novelty_criterion]
  exact not_congr (catalog.taggedQuotientCut_mem_semanticClosure_iff index)

private theorem uniqueCaptureCount_eq_zero_of_kernel_implication
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index)
    (recoverable : ∀ left right,
      (∀ other, other ≠ index ->
        (catalog.theoremAt other).primitives.agrees left right) ->
      (catalog.theoremAt index).primitives.agrees left right) :
    catalog.uniqueCaptureCount index = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro positive
  rcases (catalog.uniqueCaptureCount_pos_iff_witness index).1 positive with
    ⟨left, right, _distinct, otherAgreement, indexSeparation⟩
  exact indexSeparation (recoverable left right otherAgreement)

/-- IE-012: kernel-recoverability from the other theorems prevents escape reduction. -/
theorem lowersEscape_false_of_recoverable
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index)
    (recoverable : ∀ left right,
      (∀ other, other ≠ index ->
        (catalog.theoremAt other).primitives.agrees left right) ->
      (catalog.theoremAt index).primitives.agrees left right) :
    ¬catalog.LowersEscape index := by
  have uniqueZero :=
    catalog.uniqueCaptureCount_eq_zero_of_kernel_implication index recoverable
  have numeratorEqual := catalog.escapeNumerator_without_eq index
  rw [uniqueZero, Nat.add_zero] at numeratorEqual
  intro lowers
  unfold LowersEscape escapeRate at lowers
  rw [numeratorEqual] at lowers
  exact (lt_irrefl _ lowers)

/-- IE-013: distinct catalog entries with the same kernel both have zero unique capture. -/
theorem same_kernel_both_zero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : catalog.Index) (distinct : first ≠ second)
    (sameKernel : ∀ left right,
      (catalog.theoremAt first).primitives.agrees left right ↔
        (catalog.theoremAt second).primitives.agrees left right) :
    catalog.uniqueCaptureCount first = 0 ∧
      catalog.uniqueCaptureCount second = 0 := by
  constructor
  · apply catalog.uniqueCaptureCount_eq_zero_of_kernel_implication
    intro left right otherAgreement
    exact (sameKernel left right).2
      (otherAgreement second distinct.symm)
  · apply catalog.uniqueCaptureCount_eq_zero_of_kernel_implication
    intro left right otherAgreement
    exact (sameKernel left right).1
      (otherAgreement first distinct)

/-- IE-014: a universal agreement kernel has no unique capture. -/
theorem constant_kernel_zero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index)
    (constant : ∀ left right,
      (catalog.theoremAt index).primitives.agrees left right) :
    catalog.uniqueCaptureCount index = 0 := by
  apply catalog.uniqueCaptureCount_eq_zero_of_kernel_implication
  intro left right _
  exact constant left right

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
