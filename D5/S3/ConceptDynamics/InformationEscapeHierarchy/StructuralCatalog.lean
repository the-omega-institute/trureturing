/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Structural catalogs certify strict kernel shrinkage and agree with finite verdicts. -/

import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralArena

/- Library-search audit trail (2026-09-05):
   * Exact current-tree hits `Catalog.jointKernel`, `jointKernel_antitone`,
     `indistinguishable_iff_forall`, `uniqueCaptureCount_pos_iff_witness`, and
     `structurallyLowersEscape_iff_lowersEscape` are reused below.
   * Exact current-tree hits `CIRPT.PrimitiveBundle.agrees` and
     `agrees_equivalence` supply the finite bundle relation and reflexivity.
   * Repository searches found no arbitrary-state `StructuralCatalog` joint
     kernel, strictness certificate, triviality predicate, or finite bridge.
   * Pinned Mathlib supplies the pointwise Pi order on curried Prop-valued
     relations and `Set.ssubset_iff_exists`; no Set strict-subset operator is
     applied to a curried relation in this module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

namespace StructuralCatalog

/-- The common structural kernel of all primitive kernels belonging to the
selected theorem units. -/
def jointKernel {arena : StructuralArena.{u}}
    (catalog : StructuralCatalog.{u, v, w} arena)
    (selected : Set catalog.Index) : StructuralKernel arena.State where
  relation left right := forall index, index ∈ selected -> forall primitive,
    ((catalog.theoremAt index).primitiveKernel primitive).relation left right
  equivalence := by
    refine ⟨?_, ?_, ?_⟩
    · intro state index _ primitive
      exact ((catalog.theoremAt index).primitiveKernel primitive).equivalence.refl state
    · intro left right agreement index selectedIndex primitive
      exact ((catalog.theoremAt index).primitiveKernel primitive).equivalence.symm
        (agreement index selectedIndex primitive)
    · intro left middle right first second index selectedIndex primitive
      exact ((catalog.theoremAt index).primitiveKernel primitive).equivalence.trans
        (first index selectedIndex primitive) (second index selectedIndex primitive)

/-- A theorem structurally lowers escape when the full joint relation refines
the leave-one-out relation and the reverse refinement fails. -/
def StructurallyLowersEscape {arena : StructuralArena.{u}}
    (catalog : StructuralCatalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  let full := (catalog.jointKernel Set.univ).relation
  let without :=
    (catalog.jointKernel {candidate | candidate ≠ index}).relation
  full <= without ∧ ¬(without <= full)

end StructuralCatalog

/-- Data certifying strict structural kernel shrinkage at one catalog index. -/
structure StructuralStrictnessCertificate
    {arena : StructuralArena.{u}} (catalog : StructuralCatalog.{u, v, w} arena)
    (index : catalog.Index) where
  inclusion :
    (catalog.jointKernel Set.univ).relation <=
      (catalog.jointKernel {candidate | candidate ≠ index}).relation
  left : arena.State
  right : arena.State
  without_agrees :
    (catalog.jointKernel {candidate | candidate ≠ index}).relation left right
  full_separates :
    ¬(catalog.jointKernel Set.univ).relation left right

namespace StructuralCatalog

/-- A strictness certificate proves the structural escape-lowering verdict. -/
theorem structurallyLowersEscape_of_certificate
    {arena : StructuralArena.{u}} (catalog : StructuralCatalog.{u, v, w} arena)
    (index : catalog.Index)
    (certificate : StructuralStrictnessCertificate catalog index) :
    catalog.StructurallyLowersEscape index := by
  refine ⟨certificate.inclusion, ?_⟩
  intro reverseInclusion
  exact certificate.full_separates
    (reverseInclusion certificate.left certificate.right certificate.without_agrees)

/-- Every structural escape-lowering verdict yields a concrete strictness
certificate. -/
theorem exists_certificate_of_structurallyLowersEscape
    {arena : StructuralArena.{u}} (catalog : StructuralCatalog.{u, v, w} arena)
    (index : catalog.Index) (lowers : catalog.StructurallyLowersEscape index) :
    Nonempty (StructuralStrictnessCertificate catalog index) := by
  classical
  obtain ⟨inclusion, notReverse⟩ := lowers
  have witness : exists left right,
      (catalog.jointKernel {candidate | candidate ≠ index}).relation left right ∧
        ¬(catalog.jointKernel Set.univ).relation left right := by
    by_contra noWitness
    apply notReverse
    intro left right withoutAgreement
    by_contra fullSeparation
    exact noWitness ⟨left, right, withoutAgreement, fullSeparation⟩
  rcases witness with ⟨left, right, withoutAgreement, fullSeparation⟩
  exact ⟨{
    inclusion := inclusion
    left := left
    right := right
    without_agrees := withoutAgreement
    full_separates := fullSeparation
  }⟩

/-- Structural escape lowering is equivalent to inhabitation of its
strictness-certificate type. -/
theorem structurallyLowersEscape_iff_exists_certificate
    {arena : StructuralArena.{u}} (catalog : StructuralCatalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.StructurallyLowersEscape index ↔
      Nonempty (StructuralStrictnessCertificate catalog index) := by
  constructor
  · exact catalog.exists_certificate_of_structurallyLowersEscape index
  · rintro ⟨certificate⟩
    exact catalog.structurallyLowersEscape_of_certificate index certificate

/-- Structural triviality is failure to strictly shrink the full joint
kernel relative to the leave-one-out kernel. -/
def TrivialInCatalog {arena : StructuralArena.{u}}
    (catalog : StructuralCatalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  ¬catalog.StructurallyLowersEscape index

end StructuralCatalog

namespace Catalog

/-- Finite catalog triviality is emptiness of the theorem's unique-capture
pair set. -/
def TrivialInCatalog {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Prop :=
  catalog.uniqueCapturePairs index = ∅

/-- On a nondegenerate finite arena, empty unique capture is exactly failure
to lower escape. -/
theorem trivialInCatalog_iff_not_lowersEscape
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.TrivialInCatalog index ↔ ¬catalog.LowersEscape index := by
  constructor
  · intro trivial lowers
    have positive :=
      (catalog.lowersEscape_iff_uniqueCaptureCount_pos index nondegenerate).1 lowers
    unfold TrivialInCatalog at trivial
    unfold uniqueCaptureCount at positive
    rw [trivial] at positive
    simp at positive
  · intro notLowers
    apply Finset.card_eq_zero.mp
    change catalog.uniqueCaptureCount index = 0
    apply Nat.eq_zero_of_not_pos
    intro positive
    exact notLowers
      ((catalog.lowersEscape_iff_uniqueCaptureCount_pos index nondegenerate).2 positive)

theorem toStructuralCatalog_jointKernel_relation_iff_set
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Set catalog.Index) (left right : arena.State) :
    (catalog.toStructuralCatalog.jointKernel selected).relation left right ↔
      (left, right) ∈ catalog.jointKernel selected := by
  rfl

/-- The structural embedding of a finite selection has exactly the landed
finite indistinguishability relation. -/
theorem toStructuralCatalog_jointKernel_relation_iff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (left right : arena.State) :
    (catalog.toStructuralCatalog.jointKernel (selected : Set catalog.Index)).relation
        left right ↔
      catalog.indistinguishable selected left right := by
  rw [catalog.indistinguishable_iff_forall selected left right]
  rfl

/-- A finite unique-capture witness, with the same pair, constructs a
strictness certificate for the embedded structural catalog. -/
def toStructuralCatalog_certificate_of_uniqueCapture_witness
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (left right : arena.State)
    (_distinct : left ≠ right)
    (withoutAgreement : forall candidate, candidate ≠ index ->
      (catalog.theoremAt candidate).primitives.agrees left right)
    (indexSeparation :
      ¬(catalog.theoremAt index).primitives.agrees left right) :
    StructuralStrictnessCertificate catalog.toStructuralCatalog index where
  inclusion := by
    intro first second fullAgreement candidate candidateNe primitive
    exact fullAgreement candidate (Set.mem_univ candidate) primitive
  left := left
  right := right
  without_agrees := by
    intro candidate candidateNe primitive
    exact withoutAgreement candidate candidateNe primitive
  full_separates := by
    intro fullAgreement
    apply indexSeparation
    intro primitive
    exact fullAgreement index (Set.mem_univ index) primitive

/-- A structural certificate over an embedded finite catalog preserves its
pair and yields the landed finite unique-capture witness conditions. -/
theorem uniqueCapture_witness_of_toStructuralCatalog_certificate
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index)
    (certificate :
      StructuralStrictnessCertificate catalog.toStructuralCatalog index) :
    certificate.left ≠ certificate.right ∧
      (forall candidate, candidate ≠ index ->
        (catalog.theoremAt candidate).primitives.agrees
          certificate.left certificate.right) ∧
      ¬(catalog.theoremAt index).primitives.agrees
        certificate.left certificate.right := by
  have distinct : certificate.left ≠ certificate.right := by
    intro same
    apply certificate.full_separates
    rw [same]
    exact (catalog.toStructuralCatalog.jointKernel Set.univ).equivalence.refl
      certificate.right
  have withoutAgreement : forall candidate, candidate ≠ index ->
      (catalog.theoremAt candidate).primitives.agrees
        certificate.left certificate.right := by
    intro candidate candidateNe primitive
    exact certificate.without_agrees candidate candidateNe primitive
  have indexSeparation :
      ¬(catalog.theoremAt index).primitives.agrees
        certificate.left certificate.right := by
    intro indexAgreement
    apply certificate.full_separates
    intro candidate _ primitive
    by_cases same : candidate = index
    · subst candidate
      exact indexAgreement primitive
    · exact certificate.without_agrees candidate same primitive
  exact ⟨distinct, withoutAgreement, indexSeparation⟩

/-- Embedded structural certificates are equivalent to positive finite unique
capture, with the same pair transported in both directions. -/
theorem toStructuralCatalog_exists_certificate_iff_uniqueCaptureCount_pos
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    Nonempty (StructuralStrictnessCertificate catalog.toStructuralCatalog index) ↔
      0 < catalog.uniqueCaptureCount index := by
  constructor
  · rintro ⟨certificate⟩
    rcases catalog.uniqueCapture_witness_of_toStructuralCatalog_certificate
      index certificate with ⟨distinct, otherAgreement, indexSeparation⟩
    exact (catalog.uniqueCaptureCount_pos_iff_witness index).2
      ⟨certificate.left, certificate.right, distinct,
        otherAgreement, indexSeparation⟩
  · intro positive
    rcases (catalog.uniqueCaptureCount_pos_iff_witness index).1 positive with
      ⟨left, right, distinct, otherAgreement, indexSeparation⟩
    exact ⟨catalog.toStructuralCatalog_certificate_of_uniqueCapture_witness
      index left right distinct otherAgreement indexSeparation⟩

/-- The universal structural verdict of an embedded finite catalog agrees
with the landed finite Set-level structural verdict. -/
theorem toStructuralCatalog_structurallyLowersEscape_iff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    catalog.toStructuralCatalog.StructurallyLowersEscape index ↔
      catalog.StructurallyLowersEscape index := by
  constructor
  · intro structuralLowers
    rcases catalog.toStructuralCatalog.exists_certificate_of_structurallyLowersEscape
      index structuralLowers with ⟨certificate⟩
    rcases catalog.uniqueCapture_witness_of_toStructuralCatalog_certificate
      index certificate with ⟨_distinct, otherAgreement, indexSeparation⟩
    apply Set.ssubset_iff_exists.mpr
    refine ⟨catalog.jointKernel_antitone (Set.subset_univ _), ?_⟩
    refine ⟨(certificate.left, certificate.right), ?_, ?_⟩
    · exact otherAgreement
    · intro fullAgreement
      exact indexSeparation (fullAgreement index (Set.mem_univ index))
  · intro finiteLowers
    rcases (Set.ssubset_iff_exists.mp finiteLowers).2 with
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
    apply catalog.toStructuralCatalog.structurallyLowersEscape_of_certificate index
    exact catalog.toStructuralCatalog_certificate_of_uniqueCapture_witness
      index pair.1 pair.2 distinct
      (fun candidate candidateNe => pairInWithout candidate candidateNe)
      indexSeparation

/-- On a nondegenerate finite arena, the embedded structural verdict also
agrees with the landed exact-rate verdict. -/
theorem toStructuralCatalog_structurallyLowersEscape_iff_lowersEscape
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) (nondegenerate : arena.Nondegenerate) :
    catalog.toStructuralCatalog.StructurallyLowersEscape index ↔
      catalog.LowersEscape index :=
  (catalog.toStructuralCatalog_structurallyLowersEscape_iff index).trans
    (catalog.structurallyLowersEscape_iff_lowersEscape index nondegenerate)

end Catalog

private abbrev parityStructuralArena : StructuralArena where
  State := Nat

private def parityStructuralKernel : StructuralKernel Nat where
  relation left right := left % 2 = right % 2
  equivalence := eq_equivalence.comap fun state => state % 2

private abbrev parityStructuralUnit : StructuralTheoremUnit parityStructuralArena where
  PrimitiveIndex := Unit
  primitiveIndexFintype := inferInstance
  primitiveKernel := fun _ => parityStructuralKernel
  Statement := True
  proof := True.intro

private abbrev parityStructuralCatalog : StructuralCatalog parityStructuralArena where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := fun _ => parityStructuralUnit

/- T-035: parity on an infinite state carrier strictly refines the universal
empty-selection kernel, witnessed by zero and one without enumerating Nat. -/
example : parityStructuralCatalog.StructurallyLowersEscape () := by
  apply parityStructuralCatalog.structurallyLowersEscape_of_certificate ()
  exact {
    inclusion := by
      intro left right _ candidate candidateNe
      exact (candidateNe rfl).elim
    left := 0
    right := 1
    without_agrees := by
      intro candidate candidateNe
      exact (candidateNe rfl).elim
    full_separates := by
      intro fullAgreement
      have parityAgreement := fullAgreement () (Set.mem_univ ()) ()
      norm_num [parityStructuralCatalog, parityStructuralUnit,
        parityStructuralKernel] at parityAgreement
  }

end D5.S3.ConceptDynamics.InformationEscape
