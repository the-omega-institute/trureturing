/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extensional catalog kernels form a finite bounded lattice with certified escape increments. -/

import D5.S3.ConceptDynamics.InformationEscape.EscapePairs
import Mathlib.Data.Fintype.Lattice

/- Library-search audit trail (2026-09-05):
   * Repository searches for `GeneratedKernel`, quotient relation orders, and
     finite kernel lattices found no existing owner under `D5`.
   * Exact current-tree hits `Catalog.indistinguishable_equivalence`,
     `indistinguishable_iff_forall`, `indistinguishable_insert_iff`,
     `indistinguishable_mono`, `escapePairs`, and `offDiagonalPairs` are reused.
   * Pinned Mathlib exact hits `Quotient.finite`, `Quotient.fintype`,
     `Quotient.lift`, `Quotient.liftOn₂`, `Quotient.sound`, and
     `Bool.eq_iff_iff` provide the quotient and reflected Boolean descent.
   * No pinned declaration constructs the internal join of this generated
     closure system; it is characterized below by its least-upper-bound law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

/-- The landed selected-catalog relation, packaged with its existing decision procedure. -/
def generatedKernelRelation {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) : DecidableKernel arena.State where
  relation := catalog.indistinguishable selected
  equivalence := catalog.indistinguishable_equivalence selected
  decidableRelation := fun _ _ => catalog.indistinguishableDecidable selected _ _

/-- Two selections represent one node exactly when their relation truth tables agree. -/
def generatedKernelSetoid {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    Setoid (Finset catalog.Index) where
  r first second := ∀ left right,
    (catalog.generatedKernelRelation first).relation left right ↔
      (catalog.generatedKernelRelation second).relation left right
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro selected left right
      exact Iff.rfl
    · intro first second same left right
      exact (same left right).symm
    · intro first second third firstSecond secondThird left right
      exact (firstSecond left right).trans (secondThird left right)

/-- The finite closure family of catalog-generated kernels, quotiented extensionally. -/
def GeneratedKernel {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :=
  Quotient (generatedKernelSetoid catalog)

/-- The extensional generated-kernel node represented by a finite selection. -/
def generatedKernel {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) : catalog.GeneratedKernel :=
  Quotient.mk _ selected

namespace GeneratedKernel

/-- The exact state relation carried by a generated-kernel node. -/
def relation {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : arena.State → arena.State → Prop :=
  Quotient.lift
    (fun selected => (catalog.generatedKernelRelation selected).relation)
    (by
      intro first second same
      funext left right
      exact propext (same left right))
    node

@[simp] theorem relation_generatedKernel
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (left right : arena.State) :
    (catalog.generatedKernel selected).relation left right ↔
      catalog.indistinguishable selected left right :=
  Iff.rfl

/-- The landed Boolean relation table, descended to an extensional node. -/
def relationB {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) (left right : arena.State) : Bool :=
  Quotient.lift
    (fun selected => catalog.indistinguishableB selected left right)
    (by
      intro first second same
      apply Bool.eq_iff_iff.mpr
      rw [catalog.indistinguishableB_eq_true_iff,
        catalog.indistinguishableB_eq_true_iff]
      change
        (catalog.generatedKernelRelation first).relation left right ↔
          (catalog.generatedKernelRelation second).relation left right
      exact same left right)
    node

/-- The descended Boolean table reflects the node relation exactly. -/
theorem relationB_eq_true_iff
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) (left right : arena.State) :
    node.relationB left right = true ↔ node.relation left right := by
  induction node using Quotient.inductionOn with
  | _ selected => exact catalog.indistinguishableB_eq_true_iff selected left right

/-- Every generated-kernel relation remains decidable after quotienting. -/
instance relationDecidable
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : DecidableRel node.relation := by
  intro left right
  exact decidable_of_iff (node.relationB left right = true)
    (node.relationB_eq_true_iff left right)

/-- The finer node relates no pair that the coarser node separates. -/
def KernelRefines {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (finer coarser : catalog.GeneratedKernel) : Prop :=
  finer.relation ≤ coarser.relation

/-- Extensional equality of node relations determines equality in the quotient. -/
@[ext] theorem ext
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {first second : catalog.GeneratedKernel}
    (same : ∀ left right, first.relation left right ↔ second.relation left right) :
    first = second := by
  induction first using Quotient.inductionOn with
  | _ firstSelected =>
      induction second using Quotient.inductionOn with
      | _ secondSelected => exact Quotient.sound same

instance instLE {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    LE catalog.GeneratedKernel where
  le := KernelRefines

instance instPartialOrder {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    PartialOrder catalog.GeneratedKernel where
  le_refl node := fun _ _ related => related
  le_trans first second third firstSecond secondThird :=
    fun _ _ related => secondThird _ _ (firstSecond _ _ related)
  le_antisymm first second firstSecond secondFirst := by
    apply ext
    intro left right
    exact ⟨firstSecond left right, secondFirst left right⟩

/-- Ordered off-diagonal pairs that remain indistinguishable at this node. -/
def escapeAt {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  letI : DecidableRel node.relation := node.relationDecidable
  exact (offDiagonalPairs arena.State).filter fun pair =>
    node.relation pair.1 pair.2

/-- Escape pairs removed when moving from one node to another. -/
def edgeCapture {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (source target : catalog.GeneratedKernel) : Finset (arena.State × arena.State) := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  exact source.escapeAt \ target.escapeAt

/-- At a represented node, the node escape set is the landed catalog escape set. -/
theorem escapeAt_generatedKernel_eq_escapePairs
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) :
    (catalog.generatedKernel selected).escapeAt = catalog.escapePairs selected := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  rfl

end GeneratedKernel

private theorem indistinguishable_union_iff
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : Finset catalog.Index) (left right : arena.State) :
    catalog.indistinguishable (first ∪ second) left right ↔
      catalog.indistinguishable first left right ∧
        catalog.indistinguishable second left right := by
  letI := catalog.indexDecidableEq
  simp only [catalog.indistinguishable_iff_forall]
  constructor
  · intro agreement
    exact
      ⟨fun index membership => agreement index (Finset.mem_union_left second membership),
        fun index membership => agreement index (Finset.mem_union_right first membership)⟩
  · rintro ⟨firstAgreement, secondAgreement⟩ index membership
    rcases Finset.mem_union.mp membership with inFirst | inSecond
    · exact firstAgreement index inFirst
    · exact secondAgreement index inSecond

private def generatedKernelInf
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : catalog.GeneratedKernel) : catalog.GeneratedKernel :=
  Quotient.liftOn₂ first second
    (fun firstSelected secondSelected =>
      catalog.generatedKernel (by
        letI := catalog.indexDecidableEq
        exact firstSelected ∪ secondSelected))
    (by
      intro firstSelected secondSelected firstSelected' secondSelected' sameFirst sameSecond
      apply GeneratedKernel.ext
      intro left right
      rw [GeneratedKernel.relation_generatedKernel,
        GeneratedKernel.relation_generatedKernel,
        catalog.indistinguishable_union_iff firstSelected secondSelected,
        catalog.indistinguishable_union_iff firstSelected' secondSelected']
      exact and_congr (sameFirst left right) (sameSecond left right))

private theorem generatedKernelInf_relation_iff
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) (left right : arena.State) :
    (generatedKernelInf catalog first second).relation left right ↔
      first.relation left right ∧ second.relation left right := by
  induction first using Quotient.inductionOn with
  | _ firstSelected =>
      induction second using Quotient.inductionOn with
      | _ secondSelected =>
          exact catalog.indistinguishable_union_iff firstSelected secondSelected left right

private noncomputable def internalSupGenerators
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : catalog.GeneratedKernel) : Finset catalog.Index := by
  classical
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  exact catalog.fullIndexSet.filter fun index =>
    first.KernelRefines (catalog.generatedKernel {index}) ∧
      second.KernelRefines (catalog.generatedKernel {index})

private noncomputable def generatedKernelSup
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : catalog.GeneratedKernel) : catalog.GeneratedKernel :=
  catalog.generatedKernel (internalSupGenerators catalog first second)

private theorem le_generatedKernelSup_left
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) :
    first ≤ generatedKernelSup catalog first second := by
  classical
  intro left right related
  change catalog.indistinguishable
    (internalSupGenerators catalog first second) left right
  apply (catalog.indistinguishable_iff_forall _ left right).2
  intro index membership
  have parts := Finset.mem_filter.mp membership
  have singletonRelated := parts.2.1 left right related
  change catalog.indistinguishable {index} left right at singletonRelated
  exact (catalog.indistinguishable_iff_forall {index} left right).1
    singletonRelated index (by simp)

private theorem le_generatedKernelSup_right
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) :
    second ≤ generatedKernelSup catalog first second := by
  classical
  intro left right related
  change catalog.indistinguishable
    (internalSupGenerators catalog first second) left right
  apply (catalog.indistinguishable_iff_forall _ left right).2
  intro index membership
  have parts := Finset.mem_filter.mp membership
  have singletonRelated := parts.2.2 left right related
  change catalog.indistinguishable {index} left right at singletonRelated
  exact (catalog.indistinguishable_iff_forall {index} left right).1
    singletonRelated index (by simp)

private theorem generatedKernelSup_le
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second upper : catalog.GeneratedKernel)
    (firstUpper : first ≤ upper) (secondUpper : second ≤ upper) :
    generatedKernelSup catalog first second ≤ upper := by
  classical
  induction upper using Quotient.inductionOn with
  | _ selected =>
      intro left right related
      change catalog.indistinguishable
        (internalSupGenerators catalog first second) left right at related
      change catalog.indistinguishable selected left right
      apply catalog.indistinguishable_mono (larger := internalSupGenerators catalog first second)
        (smaller := selected) ?_ related
      intro index membership
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ index, ?_⟩
      have selectedRefinesSingleton :
          catalog.generatedKernel selected ≤ catalog.generatedKernel {index} := by
        intro x y selectedRelated
        change catalog.indistinguishable selected x y at selectedRelated
        change catalog.indistinguishable {index} x y
        apply catalog.indistinguishable_mono (larger := selected)
          (smaller := {index}) ?_ selectedRelated
        simpa using membership
      exact
        ⟨le_trans firstUpper selectedRefinesSingleton,
          le_trans secondUpper selectedRefinesSingleton⟩

noncomputable instance instLattice
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    Lattice catalog.GeneratedKernel where
  inf := generatedKernelInf catalog
  inf_le_left first second := fun left right related =>
    (generatedKernelInf_relation_iff first second left right).1 related |>.1
  inf_le_right first second := fun left right related =>
    (generatedKernelInf_relation_iff first second left right).1 related |>.2
  le_inf first second third firstSecond firstThird := fun left right related =>
    (generatedKernelInf_relation_iff second third left right).2
      ⟨firstSecond left right related, firstThird left right related⟩
  sup := generatedKernelSup catalog
  le_sup_left := le_generatedKernelSup_left
  le_sup_right := le_generatedKernelSup_right
  sup_le := generatedKernelSup_le

private theorem le_generatedKernel_empty
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : node ≤ catalog.generatedKernel ∅ := by
  intro left right _
  rw [GeneratedKernel.relation_generatedKernel]
  exact (catalog.indistinguishable_iff_forall ∅ left right).2 (by simp)

private theorem generatedKernel_full_le
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) :
    catalog.generatedKernel catalog.fullIndexSet ≤ node := by
  induction node using Quotient.inductionOn with
  | _ selected =>
      intro left right related
      change catalog.indistinguishable catalog.fullIndexSet left right at related
      change catalog.indistinguishable selected left right
      apply catalog.indistinguishable_mono (larger := catalog.fullIndexSet)
        (smaller := selected) ?_ related
      intro index _
      exact Finset.mem_univ index

noncomputable instance instBoundedOrder
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    BoundedOrder catalog.GeneratedKernel where
  top := catalog.generatedKernel ∅
  le_top := le_generatedKernel_empty
  bot := catalog.generatedKernel catalog.fullIndexSet
  bot_le := generatedKernel_full_le

instance instFinite
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    Finite catalog.GeneratedKernel := by
  letI := catalog.indexFintype
  exact Quotient.finite _

noncomputable instance instFintype
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    Fintype catalog.GeneratedKernel := by
  classical
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  exact Quotient.fintype _

/-- IE-040: union of generators computes relation intersection, hence lattice meet. -/
theorem generatedKernel_union
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : Finset catalog.Index) :
    catalog.generatedKernel (by
      letI := catalog.indexDecidableEq
      exact first ∪ second) =
      catalog.generatedKernel first ⊓ catalog.generatedKernel second := by
  rfl

/-- IE-041: the extensional generated family carries the finite lattice instances above. -/
theorem generatedKernel_finite_lattice
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    Finite catalog.GeneratedKernel :=
  inferInstance

/-- The greatest node is generated by the empty selection. -/
theorem top_eq_generatedKernel_empty
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (⊤ : catalog.GeneratedKernel) = catalog.generatedKernel ∅ :=
  rfl

/-- The least node is generated by the full catalog. -/
theorem bot_eq_generatedKernel_full
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (⊥ : catalog.GeneratedKernel) = catalog.generatedKernel catalog.fullIndexSet :=
  rfl

/-- Lattice meet of represented nodes is generated by unioning their generators. -/
theorem inf_eq_generatedKernel_union
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (first second : Finset catalog.Index) :
    catalog.generatedKernel first ⊓ catalog.generatedKernel second =
      catalog.generatedKernel (by
        letI := catalog.indexDecidableEq
        exact first ∪ second) := by
  exact (catalog.generatedKernel_union first second).symm

/-- Lattice infimum is the greatest lower bound of its two operands. -/
theorem isGLB_inf
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) :
    IsGLB {first, second} (first ⊓ second) := by
  constructor
  · intro node membership
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at membership
    rcases membership with same | same
    · subst node
      exact inf_le_left
    · subst node
      exact inf_le_right
  · intro node lower
    exact le_inf (lower (by simp)) (lower (by simp))

/-- The internally generated supremum is the least generated upper bound. -/
theorem isLUB_sup
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) :
    IsLUB {first, second} (first ⊔ second) := by
  constructor
  · intro node membership
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at membership
    rcases membership with same | same
    · subst node
      exact le_sup_left
    · subst node
      exact le_sup_right
  · intro node upper
    exact sup_le (upper (by simp)) (upper (by simp))

/-- Adding one generator to a represented node, with its certified downward refinement. -/
def GeneratorStep {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (source target : catalog.GeneratedKernel) (added : catalog.Index) : Prop := by
  letI := catalog.indexDecidableEq
  exact ∃ selected,
    catalog.generatedKernel selected = source ∧
      catalog.generatedKernel (insert added selected) = target ∧
      target.KernelRefines source

/-- A generator step is strict when its reverse refinement fails. -/
def StrictGeneratorStep {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (source target : catalog.GeneratedKernel) (added : catalog.Index) : Prop :=
  catalog.GeneratorStep source target added ∧ ¬source.KernelRefines target

/-- A generator addition that leaves its extensional node unchanged. -/
def CollapsedAddition {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (node : catalog.GeneratedKernel) (added : catalog.Index) : Prop :=
  catalog.GeneratorStep node node added

/-- IE-042: adding a fixed generator respects extensional node equality. -/
theorem generatorStep_wellDefined
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {first second : Finset catalog.Index} (added : catalog.Index)
    (same : catalog.generatedKernel first = catalog.generatedKernel second) :
    catalog.generatedKernel (by
      letI := catalog.indexDecidableEq
      exact insert added first) =
      catalog.generatedKernel (by
        letI := catalog.indexDecidableEq
        exact insert added second) := by
  apply GeneratedKernel.ext
  intro left right
  rw [GeneratedKernel.relation_generatedKernel,
    GeneratedKernel.relation_generatedKernel,
    catalog.indistinguishable_insert_iff first added,
    catalog.indistinguishable_insert_iff second added]
  exact and_congr Iff.rfl (by
    change (catalog.generatedKernel first).relation left right ↔
      (catalog.generatedKernel second).relation left right
    rw [same])

/-- IE-043: every certified generator step can only remove escape pairs. -/
theorem escape_antitone_on_step
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} {added : catalog.Index}
    (step : catalog.GeneratorStep source target added) :
    target.escapeAt ⊆ source.escapeAt := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  rcases step with ⟨selected, sourceEq, targetEq, refinement⟩
  intro pair membership
  have parts := Finset.mem_filter.mp membership
  apply Finset.mem_filter.mpr
  exact ⟨parts.1, refinement pair.1 pair.2 parts.2⟩

/-- IE-044: strict shrinkage on a generator step is exactly a nonempty increment. -/
theorem strict_kernel_iff_nonempty_increment
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} {added : catalog.Index}
    (step : catalog.GeneratorStep source target added) :
    ¬source.KernelRefines target ↔ source.edgeCapture target ≠ ∅ := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  constructor
  · intro notReverse emptyCapture
    apply notReverse
    intro left right sourceRelated
    by_contra notToRelated
    have distinct : left ≠ right := by
      intro same
      subst right
      exact notToRelated (by
        induction target using Quotient.inductionOn with
        | _ selected => exact (catalog.indistinguishable_equivalence selected).refl left)
    have inFromEscape : (left, right) ∈ source.escapeAt := by
      apply Finset.mem_filter.mpr
      exact ⟨by simp [offDiagonalPairs, distinct], sourceRelated⟩
    have inCapture : (left, right) ∈ source.edgeCapture target := by
      apply Finset.mem_sdiff.mpr
      refine ⟨inFromEscape, ?_⟩
      intro inToEscape
      exact notToRelated (Finset.mem_filter.mp inToEscape).2
    rw [emptyCapture] at inCapture
    simp at inCapture
  · intro nonempty reverse
    apply nonempty
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨pair, membership⟩
    have parts := Finset.mem_sdiff.mp membership
    exact parts.2 (by
      have sourceParts := Finset.mem_filter.mp parts.1
      apply Finset.mem_filter.mpr
      exact ⟨sourceParts.1, reverse pair.1 pair.2 sourceParts.2⟩)

/-- The count form of IE-044: strict shrinkage is equivalent to positive capture. -/
theorem strict_kernel_iff_edgeCapture_card_pos
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} {added : catalog.Index}
    (step : catalog.GeneratorStep source target added) :
    ¬source.KernelRefines target ↔ 0 < (source.edgeCapture target).card := by
  rw [catalog.strict_kernel_iff_nonempty_increment step, Finset.card_pos,
    Finset.nonempty_iff_ne_empty]

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
