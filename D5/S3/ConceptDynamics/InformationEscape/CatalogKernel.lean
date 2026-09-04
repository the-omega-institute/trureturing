/- GID: D5/S3/ConceptDynamics/InformationEscape/CatalogKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CatalogKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Selected theorem bundles compute an antitone canonical joint kernel. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Finset.Fold

/- Library-search audit trail (2026-09-04):
   * Repository searches for catalog indistinguishability, finite Boolean
     reflection, and catalog joint kernels found no existing engine owner.
   * Exact current-tree hit `CIRPT.PrimitiveBundle.agreesB_eq_true_iff` is
     reused for each theorem bundle, and `quotient_cut_kernel_normal_form`
     transports its packaged relation to quotient equality.
   * Exact current-tree hit
     `Faithfulness.JointFaithfulnessLeibnizCriterion.jointKernel` is the
     canonical dependent-family kernel and is reused in the bridge below.
   * `DefinitionKernelGalois.jointKernel_antitone` has the same order pattern
     for subsets of one homogeneous concept family, but does not directly
     typecheck for changing subtype indices with dependent quotient outputs;
     the catalog specialization is therefore proved elementwise.
   * Pinned Mathlib exact hits `Finset.fold_op_rel_iff_and`,
     `Set.mem_iInter`, `Set.mem_insert_iff`, and `Finset.mem_insert` supply the
     finite reflection and insertion decompositions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

namespace Catalog

/-- Two states are indistinguishable by every theorem in a finite selection. -/
def indistinguishable {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (left right : arena.State) : Prop :=
  forall index, index ∈ selected ->
    (catalog.theoremAt index).primitives.agrees left right

/-- Executable finite reflection of selected-catalog indistinguishability. -/
def indistinguishableB {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (left right : arena.State) : Bool :=
  let _ := catalog.indexDecidableEq
  Finset.fold (fun first second => first && second) true
    (fun index => (catalog.theoremAt index).primitives.agreesB left right) selected

/-- The selected finite Boolean test reflects propositional indistinguishability. -/
theorem indistinguishableB_eq_true_iff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (left right : arena.State) :
    catalog.indistinguishableB selected left right = true <->
      catalog.indistinguishable selected left right := by
  letI := catalog.indexDecidableEq
  unfold indistinguishableB indistinguishable
  have foldCharacterization :=
    Finset.fold_op_rel_iff_and
      (op := fun first second : Bool => first && second)
      (r := fun _ actual : Bool => actual = true)
      (b := true)
      (f := fun index =>
        (catalog.theoremAt index).primitives.agreesB left right)
      (s := selected) (c := true) (by
        intro expected first second
        simp)
  simpa only [PrimitiveBundle.agreesB_eq_true_iff, true_and] using foldCharacterization

/-- Indistinguishability is decidable by the reflected finite Boolean fold. -/
instance indistinguishableDecidable
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (left right : arena.State) :
    Decidable (catalog.indistinguishable selected left right) :=
  decidable_of_iff' (catalog.indistinguishableB selected left right = true)
    (catalog.indistinguishableB_eq_true_iff selected left right).symm

/-- Every selected-catalog indistinguishability relation is an equivalence. -/
theorem indistinguishable_equivalence
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) :
    Equivalence (catalog.indistinguishable selected) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x index selectedIndex
    exact (catalog.theoremAt index).primitives.agrees_equivalence.refl x
  · intro x y agreement index selectedIndex
    exact (catalog.theoremAt index).primitives.agrees_equivalence.symm
      (agreement index selectedIndex)
  · intro x y z first second index selectedIndex
    exact (catalog.theoremAt index).primitives.agrees_equivalence.trans
      (first index selectedIndex) (second index selectedIndex)

/-- The Set-level common kernel of a selected theorem subfamily. -/
def jointKernel {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Set catalog.Index) : Set (arena.State × arena.State) :=
  {pair | forall index, index ∈ selected ->
    (catalog.theoremAt index).primitives.agrees pair.1 pair.2}

/-- The catalog kernel is the canonical joint kernel of bundle quotient CUTs. -/
theorem jointKernel_eq_canonical_jointKernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Set catalog.Index) :
    catalog.jointKernel selected =
      D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointKernel
        (fun index : selected =>
          (catalog.theoremAt index.1).primitives.toKernel.quotientCut) := by
  ext pair
  constructor
  · intro agreement
    apply Set.mem_iInter.2
    intro index
    change
      (catalog.theoremAt index.1).primitives.toKernel.quotientCut pair.1 =
        (catalog.theoremAt index.1).primitives.toKernel.quotientCut pair.2
    exact (quotient_cut_kernel_normal_form
      (catalog.theoremAt index.1).primitives.toKernel pair.1 pair.2).1
        (agreement index.1 index.2)
  · intro kernelMembership index selectedIndex
    have indexMembership := Set.mem_iInter.1 kernelMembership
      ⟨index, selectedIndex⟩
    change
      (catalog.theoremAt index).primitives.toKernel.quotientCut pair.1 =
        (catalog.theoremAt index).primitives.toKernel.quotientCut pair.2 at indexMembership
    exact (quotient_cut_kernel_normal_form
      (catalog.theoremAt index).primitives.toKernel pair.1 pair.2).2 indexMembership

/-- IE-001: enlarging the selected theorem set can only shrink its joint kernel. -/
theorem jointKernel_antitone
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {smaller larger : Set catalog.Index} (subset : smaller ⊆ larger) :
    catalog.jointKernel larger ⊆ catalog.jointKernel smaller := by
  intro pair largerAgreement index smallerIndex
  exact largerAgreement index (subset smallerIndex)

/-- IE-003: inserting one theorem intersects its agreement kernel with the old kernel. -/
theorem jointKernel_insert
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (selected : Set catalog.Index) :
    catalog.jointKernel (Set.insert index selected) =
      catalog.jointKernel selected ∩
        {pair | (catalog.theoremAt index).primitives.agrees pair.1 pair.2} := by
  ext pair
  change
    (forall candidate, candidate ∈ Set.insert index selected ->
      (catalog.theoremAt candidate).primitives.agrees pair.1 pair.2) <->
      (forall candidate, candidate ∈ selected ->
        (catalog.theoremAt candidate).primitives.agrees pair.1 pair.2) /\
        (catalog.theoremAt index).primitives.agrees pair.1 pair.2
  constructor
  · intro agreement
    exact
      ⟨fun candidate selectedCandidate =>
          agreement candidate (Set.mem_insert_of_mem index selectedCandidate),
        agreement index (Set.mem_insert index selected)⟩
  · rintro ⟨selectedAgreement, indexAgreement⟩ candidate insertedCandidate
    rcases Set.mem_insert_iff.mp insertedCandidate with rfl | selectedCandidate
    · exact indexAgreement
    · exact selectedAgreement candidate selectedCandidate

/-- Restricting a finite selection preserves every agreement of the larger selection. -/
theorem indistinguishable_mono
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {smaller larger : Finset catalog.Index} (subset : smaller ⊆ larger)
    {left right : arena.State} :
    catalog.indistinguishable larger left right ->
      catalog.indistinguishable smaller left right := by
  intro agreement index smallerIndex
  exact agreement index (subset smallerIndex)

/-- Finite insertion adds exactly one bundle-agreement conjunct. -/
theorem indistinguishable_insert_iff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (index : catalog.Index)
    (left right : arena.State) :
    catalog.indistinguishable
        (let _ := catalog.indexDecidableEq; insert index selected) left right <->
      (catalog.theoremAt index).primitives.agrees left right /\
        catalog.indistinguishable selected left right := by
  letI := catalog.indexDecidableEq
  constructor
  · intro agreement
    exact
      ⟨agreement index (Finset.mem_insert_self index selected),
        fun candidate selectedCandidate =>
          agreement candidate (Finset.mem_insert_of_mem selectedCandidate)⟩
  · rintro ⟨indexAgreement, selectedAgreement⟩ candidate insertedCandidate
    rcases Finset.mem_insert.mp insertedCandidate with rfl | selectedCandidate
    · exact indexAgreement
    · exact selectedAgreement candidate selectedCandidate

end Catalog

private abbrev kernelFixtureArena : Arena :=
  Arena.ofFintype (Bool × Bool)

private abbrev kernelFixtureBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.fst⟩

private abbrev kernelFixtureUnit : TheoremUnit kernelFixtureArena where
  primitives := kernelFixtureBundle
  Statement := True
  proof := True.intro

private abbrev kernelFixtureCatalog : Catalog kernelFixtureArena :=
  Catalog.ofVector fun _ : Fin 1 => kernelFixtureUnit

/- The executable fold accepts a pair with the same first coordinate. -/
example :
    kernelFixtureCatalog.indistinguishableB kernelFixtureCatalog.fullIndexSet
      (false, false) (false, true) = true := by
  decide

/- The executable fold rejects a pair with different first coordinates. -/
example :
    kernelFixtureCatalog.indistinguishableB kernelFixtureCatalog.fullIndexSet
      (false, false) (true, false) = false := by
  decide

end D5.S3.ConceptDynamics.InformationEscape
