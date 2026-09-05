/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hasse paths characterize chain hierarchies, with length bounded by arena size. -/

import D5.S3.ConceptDynamics.InformationEscapeHierarchy.AnalysisLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.KernelChain
import D5.S3.ConceptDynamics.Refinement.StrictRefinementBound
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Comparable
import Mathlib.Order.SuccPred.LinearLocallyFinite

/- Library-search audit trail (2026-09-05):
   * Repository searches for `hasse_path`, `CovBy`, strict kernel-chain
     lengths, quotient class counts, and nested unique capture found the
     exact frozen sharp bound
     `Refinement.StrictRefinementBound.strict_refinement_steps_le_card_sub_initial_image`,
     which is applied below rather than reproved.
   * Exact current-tree hits `Catalog.GeneratedKernel.relationB_eq_true_iff`,
     `Catalog.escape_antitone_on_step`, `Catalog.uniqueCapturePairs`, and
     `Catalog.indistinguishable_mono` supply the kernel/readout and escape bridges.
   * Pinned Mathlib exact hits `SimpleGraph.hasse`,
     `SimpleGraph.hasse_preconnected_of_succ`, `LT.lt.exists_covby_le`,
     `CovBy.unique_left`, and `CovBy.unique_right` supply the cover graph.
   * Pinned Mathlib's `Setoid.map_of_le`,
     `Fintype.card_lt_of_surjective_not_injective`, and
     `Fintype.card_quotient_le` were checked as the direct quotient-card route;
     the frozen readout-range theorem already packages that same argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Refinement.StrictRefinementBound

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog.GeneratedKernel

/-- The Hasse cover relation, oriented from a finer node to the node immediately above it. -/
def IsCover {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (finer coarser : catalog.GeneratedKernel) : Prop :=
  finer ⋖ coarser

/-- The Hasse graph is a path when it is connected and has at most one cover in each direction. -/
def HasHassePath {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) : Prop :=
  (SimpleGraph.hasse catalog.GeneratedKernel).Preconnected ∧
    (∀ node : catalog.GeneratedKernel,
      {coarser : catalog.GeneratedKernel | IsCover node coarser}.Subsingleton) ∧
    (∀ node : catalog.GeneratedKernel,
      {finer : catalog.GeneratedKernel | IsCover finer node}.Subsingleton)

/-- Generator kernels are pairwise comparable after passage to extensional closure nodes. -/
def GeneratorsComparableAfterClosure {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Prop :=
  ∀ first second : catalog.Index,
    catalog.generatedKernel {first} ≤ catalog.generatedKernel {second} ∨
      catalog.generatedKernel {second} ≤ catalog.generatedKernel {first}

end Catalog.GeneratedKernel

private instance generatedKernelDecidableEq
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena} :
    DecidableEq catalog.GeneratedKernel := fun first second =>
  decidable_of_iff
    (∀ left right, first.relationB left right = second.relationB left right)
    (by
      constructor
      · intro sameTable
        apply Catalog.GeneratedKernel.ext
        intro left right
        constructor
        · intro related
          apply (second.relationB_eq_true_iff left right).1
          rw [← sameTable left right]
          exact (first.relationB_eq_true_iff left right).2 related
        · intro related
          apply (first.relationB_eq_true_iff left right).1
          rw [sameTable left right]
          exact (second.relationB_eq_true_iff left right).2 related
      · intro same
        subst second
        exact fun _ _ => rfl)

private instance generatedKernelLEDecidable
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) : Decidable (first ≤ second) :=
  decidable_of_iff
    (∀ left right,
      first.relationB left right = true → second.relationB left right = true)
    (by
      constructor
      · intro reflected left right related
        apply (second.relationB_eq_true_iff left right).1
        exact reflected left right
          ((first.relationB_eq_true_iff left right).2 related)
      · intro refinement left right reflected
        apply (second.relationB_eq_true_iff left right).2
        exact refinement left right
          ((first.relationB_eq_true_iff left right).1 reflected))

private instance generatedKernelLTDecidable
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : catalog.GeneratedKernel) : Decidable (first < second) := by
  change Decidable (first ≤ second ∧ ¬second ≤ first)
  infer_instance

private theorem generatedKernel_eq_top_or_eq_singleton
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (comparable : Catalog.GeneratedKernel.GeneratorsComparableAfterClosure catalog)
    (selected : Finset catalog.Index) :
    catalog.generatedKernel selected = ⊤ ∨
      ∃ index ∈ selected,
        catalog.generatedKernel selected = catalog.generatedKernel {index} := by
  classical
  induction selected using Finset.induction with
  | empty =>
      exact Or.inl (Catalog.top_eq_generatedKernel_empty catalog).symm
  | @insert added selected notMem inductionHypothesis =>
      have insertFormula :
          catalog.generatedKernel (insert added selected) =
            catalog.generatedKernel {added} ⊓ catalog.generatedKernel selected := by
        simpa only [Finset.singleton_union] using
          catalog.generatedKernel_union {added} selected
      rcases inductionHypothesis with selectedTop | ⟨index, indexMem, selectedSingleton⟩
      · right
        refine ⟨added, Finset.mem_insert_self added selected, ?_⟩
        rw [insertFormula, selectedTop, inf_top_eq]
      · rcases comparable added index with addedLe | indexLe
        · right
          refine ⟨added, Finset.mem_insert_self added selected, ?_⟩
          rw [insertFormula, selectedSingleton, inf_eq_left.2 addedLe]
        · right
          refine ⟨index, Finset.mem_insert_of_mem indexMem, ?_⟩
          rw [insertFormula, selectedSingleton, inf_eq_right.2 indexLe]

private theorem generatedKernel_chain_iff_generators_comparable
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (∀ first second : catalog.GeneratedKernel, first ≤ second ∨ second ≤ first) ↔
      Catalog.GeneratedKernel.GeneratorsComparableAfterClosure catalog := by
  constructor
  · intro comparable first second
    exact comparable (catalog.generatedKernel {first}) (catalog.generatedKernel {second})
  · intro comparable first second
    induction first using Quotient.inductionOn with
    | _ firstSelected =>
        induction second using Quotient.inductionOn with
        | _ secondSelected =>
            rcases generatedKernel_eq_top_or_eq_singleton catalog comparable firstSelected with
              firstTop | ⟨firstIndex, _, firstSingleton⟩
            · right
              change catalog.generatedKernel secondSelected ≤
                catalog.generatedKernel firstSelected
              rw [firstTop]
              exact le_top
            rcases generatedKernel_eq_top_or_eq_singleton catalog comparable secondSelected with
              secondTop | ⟨secondIndex, _, secondSingleton⟩
            · left
              change catalog.generatedKernel firstSelected ≤
                catalog.generatedKernel secondSelected
              rw [secondTop]
              exact le_top
            change
              catalog.generatedKernel firstSelected ≤ catalog.generatedKernel secondSelected ∨
                catalog.generatedKernel secondSelected ≤ catalog.generatedKernel firstSelected
            rw [firstSingleton, secondSingleton]
            exact comparable firstIndex secondIndex

/-- IE-041: the Hasse graph is a path exactly for a chain, equivalently when
all singleton generator kernels are comparable after extensional closure. -/
theorem hasse_path_iff_chain
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    (Catalog.GeneratedKernel.HasHassePath catalog ↔
      ∀ first second : catalog.GeneratedKernel,
        first ≤ second ∨ second ≤ first) ∧
    ((∀ first second : catalog.GeneratedKernel,
        first ≤ second ∨ second ≤ first) ↔
      Catalog.GeneratedKernel.GeneratorsComparableAfterClosure catalog) := by
  let Chain := ∀ first second : catalog.GeneratedKernel,
    first ≤ second ∨ second ≤ first
  have chain_implies_hasse_path : Chain →
      Catalog.GeneratedKernel.HasHassePath catalog := by
    intro comparable
    classical
    letI : LinearOrder catalog.GeneratedKernel :=
      Relation.linearOrderOfSymmGen comparable
    letI : LocallyFiniteOrder catalog.GeneratedKernel :=
      Fintype.toLocallyFiniteOrder
    letI : SuccOrder catalog.GeneratedKernel :=
      LinearLocallyFiniteOrder.succOrder catalog.GeneratedKernel
    refine ⟨SimpleGraph.hasse_preconnected_of_succ _, ?_, ?_⟩
    · intro node first firstMem second secondMem
      exact CovBy.unique_right
        (show node ⋖ first from firstMem) (show node ⋖ second from secondMem)
    · intro node first firstMem second secondMem
      exact CovBy.unique_left
        (show first ⋖ node from firstMem) (show second ⋖ node from secondMem)
  have hasse_path_implies_chain :
      Catalog.GeneratedKernel.HasHassePath catalog → Chain := by
    intro path first second
    by_contra notComparable
    have firstNotSecond : ¬first ≤ second := by
      intro firstSecond
      exact notComparable (Or.inl firstSecond)
    have secondNotFirst : ¬second ≤ first := by
      intro secondFirst
      exact notComparable (Or.inr secondFirst)
    have meetLtFirst : first ⊓ second < first := by
      apply lt_of_le_of_ne inf_le_left
      intro same
      apply firstNotSecond
      rw [← same]
      exact inf_le_right
    have meetLtSecond : first ⊓ second < second := by
      apply lt_of_le_of_ne inf_le_right
      intro same
      apply secondNotFirst
      rw [← same]
      exact inf_le_left
    obtain ⟨towardFirst, firstCover, towardFirstLe⟩ :=
      meetLtFirst.exists_covby_le
    obtain ⟨towardSecond, secondCover, towardSecondLe⟩ :=
      meetLtSecond.exists_covby_le
    have coversEqual : towardFirst = towardSecond :=
      path.2.1 (first ⊓ second) firstCover secondCover
    have towardFirstLeMeet : towardFirst ≤ first ⊓ second := by
      apply le_inf towardFirstLe
      simpa [coversEqual] using towardSecondLe
    exact firstCover.lt.not_ge towardFirstLeMeet
  exact
    ⟨⟨hasse_path_implies_chain, chain_implies_hasse_path⟩,
      generatedKernel_chain_iff_generators_comparable catalog⟩

private abbrev shortcutArena : Arena := Arena.ofFintype (Bool × Bool)

private abbrev shortcutConstantBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel (fun _ : Bool × Bool => false)⟩

private abbrev shortcutFirstBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.fst⟩

private abbrev shortcutIdentityBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel id⟩

private abbrev shortcutUnit (bundle : PrimitiveBundle (Bool × Bool)) :
    TheoremUnit shortcutArena where
  primitives := bundle
  Statement := True
  proof := True.intro

private abbrev shortcutCatalog : Catalog shortcutArena :=
  Catalog.ofVector fun index : Fin 3 =>
    if index = 0 then shortcutUnit shortcutConstantBundle
    else if index = 1 then shortcutUnit shortcutFirstBundle
    else shortcutUnit shortcutIdentityBundle

private theorem shortcutCatalog_chain :
    ∀ first second : shortcutCatalog.GeneratedKernel,
      first ≤ second ∨ second ≤ first := by
  intro first second
  induction first using Quotient.inductionOn with
  | _ firstSelected =>
      induction second using Quotient.inductionOn with
      | _ secondSelected =>
          have concrete : ∀ left right : Finset (Fin 3),
              shortcutCatalog.generatedKernel left ≤ shortcutCatalog.generatedKernel right ∨
              shortcutCatalog.generatedKernel right ≤
                shortcutCatalog.generatedKernel left := by
            decide
          exact concrete firstSelected secondSelected

private theorem shortcutCatalog_strict_step :
    shortcutCatalog.StrictGeneratorStep
      (shortcutCatalog.generatedKernel ∅)
      (shortcutCatalog.generatedKernel shortcutCatalog.fullIndexSet) 2 := by
  constructor
  · refine ⟨∅, rfl, ?_, ?_⟩
    · decide
    · change shortcutCatalog.generatedKernel shortcutCatalog.fullIndexSet ≤
        shortcutCatalog.generatedKernel ∅
      rw [← Catalog.top_eq_generatedKernel_empty]
      exact le_top
  · change ¬shortcutCatalog.generatedKernel ∅ ≤
      shortcutCatalog.generatedKernel shortcutCatalog.fullIndexSet
    decide

private theorem shortcutCatalog_not_cover :
    ¬Catalog.GeneratedKernel.IsCover
      (shortcutCatalog.generatedKernel shortcutCatalog.fullIndexSet)
      (shortcutCatalog.generatedKernel ∅) := by
  apply not_covBy_of_lt_of_lt
    (b := shortcutCatalog.generatedKernel {1})
  · decide
  · decide

/-- IE-041 explicit remark: a three-generator chain still has a strict
empty-to-full generator shortcut which is not a Hasse cover. -/
theorem strict_generator_dag_shortcut_not_cover :
    (∀ first second : shortcutCatalog.GeneratedKernel,
      first ≤ second ∨ second ≤ first) ∧
    shortcutCatalog.StrictGeneratorStep
      (shortcutCatalog.generatedKernel ∅)
      (shortcutCatalog.generatedKernel shortcutCatalog.fullIndexSet) 2 ∧
    ¬Catalog.GeneratedKernel.IsCover
      (shortcutCatalog.generatedKernel shortcutCatalog.fullIndexSet)
      (shortcutCatalog.generatedKernel ∅) := by
  exact ⟨shortcutCatalog_chain, shortcutCatalog_strict_step,
    shortcutCatalog_not_cover⟩

private def kernelProfile
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : Concept arena.State (arena.State → Bool) :=
  fun left right => node.relationB left right

private theorem generatedKernel_relation_equivalence
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) : Equivalence node.relation := by
  induction node using Quotient.inductionOn with
  | _ selected => exact catalog.indistinguishable_equivalence selected

private theorem kernelProfile_eq_iff_relation
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (node : catalog.GeneratedKernel) (left right : arena.State) :
    kernelProfile node left = kernelProfile node right ↔ node.relation left right := by
  let equivalence := generatedKernel_relation_equivalence node
  constructor
  · intro profilesEqual
    have atRight := congrFun profilesEqual right
    have rightReflexive : node.relationB right right = true :=
      (node.relationB_eq_true_iff right right).2 (equivalence.1 right)
    apply (node.relationB_eq_true_iff left right).1
    exact atRight.trans rightReflexive
  · intro related
    funext probe
    apply Bool.eq_iff_iff.mpr
    change node.relationB left probe = true ↔
      node.relationB right probe = true
    rw [node.relationB_eq_true_iff, node.relationB_eq_true_iff]
    constructor
    · intro leftProbe
      exact equivalence.trans (equivalence.symm related) leftProbe
    · intro rightProbe
      exact equivalence.trans related rightProbe

private theorem strictStep_strictlyRefines_kernelProfile
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} {added : catalog.Index}
    (step : catalog.StrictGeneratorStep source target added) :
    StrictlyRefines (kernelProfile source) (kernelProfile target) := by
  have relationWitness : ∃ left right,
      source.relation left right ∧ ¬target.relation left right := by
    by_contra noWitness
    apply step.2
    intro left right sourceRelated
    by_contra targetSeparated
    exact noWitness ⟨left, right, sourceRelated, targetSeparated⟩
  constructor
  · intro left right targetSame
    apply (kernelProfile_eq_iff_relation source left right).2
    exact step.1.choose_spec.2.2 left right
      ((kernelProfile_eq_iff_relation target left right).1 targetSame)
  · obtain ⟨left, right, sourceRelated, targetSeparated⟩ := relationWitness
    exact ⟨left, right,
      (kernelProfile_eq_iff_relation source left right).2 sourceRelated,
      fun targetSame => targetSeparated
        ((kernelProfile_eq_iff_relation target left right).1 targetSame)⟩

/-- IE-041: every strict generated-kernel chain has at most one fewer step
than the number of arena states. -/
theorem strict_chain_length_le_card_sub_one
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (chain : StrictKernelChain catalog) :
    chain.length ≤ arena.card - 1 := by
  by_cases noSteps : chain.length = 0
  · simp [noSteps]
  · have positiveLength : 0 < chain.length := Nat.pos_of_ne_zero noSteps
    have strictProfiles : ∀ index : Fin chain.length,
        StrictlyRefines
          (kernelProfile (chain.node index.castSucc))
          (kernelProfile (chain.node index.succ)) :=
      fun index => strictStep_strictlyRefines_kernelProfile (chain.step index)
    have rangeBound := strict_refinement_steps_le_card_sub_initial_image
      chain.length (fun index => kernelProfile (chain.node index)) strictProfiles
    have stateNonempty : Nonempty arena.State := by
      have firstStep := chain.step (⟨0, positiveLength⟩ : Fin chain.length)
      have strictProfile := strictStep_strictlyRefines_kernelProfile firstStep
      exact ⟨strictProfile.2.choose⟩
    let firstState : arena.State := Classical.choice stateNonempty
    have firstRangeNonempty : (Set.range (kernelProfile (chain.node 0))).Nonempty :=
      ⟨kernelProfile (chain.node 0) firstState, firstState, rfl⟩
    have oneLeInitial : 1 ≤ Nat.card (Set.range (kernelProfile (chain.node 0))) :=
      by
        have positive :=
          (Set.natCard_pos (Finite.Set.finite_range _)).2 firstRangeNonempty
        omega
    have subtractMonotone :
        Nat.card arena.State - Nat.card (Set.range (kernelProfile (chain.node 0))) ≤
          Nat.card arena.State - 1 :=
      Nat.sub_le_sub_left oneLeInitial _
    exact (rangeBound.trans subtractMonotone).trans_eq (by
      simp [Arena.card, Nat.card_eq_fintype_card])

/-- IE-050: if another generator is finer than `i`, then the coarser
generator `i` has no flat leave-one-out unique captures. -/
theorem nested_flat_coarse_zero
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {i j : catalog.Index} (different : i ≠ j)
    (refines : catalog.generatedKernel {j} ≤ catalog.generatedKernel {i}) :
    catalog.uniqueCapturePairs i = ∅ := by
  apply catalog.kernelRefines_implies_zero_uniqueCapture (Ne.symm different)
  intro left right agreesJ
  have singletonJ : catalog.indistinguishable {j} left right :=
    (catalog.indistinguishable_iff_forall {j} left right).2
      (by
        intro index indexMem
        have same : index = j := Finset.mem_singleton.mp indexMem
        simpa [same] using agreesJ)
  have singletonI : catalog.indistinguishable {i} left right :=
    refines left right singletonJ
  exact (catalog.indistinguishable_iff_forall {i} left right).1
    singletonI i (by simp)

private abbrev e1Arena : Arena := Arena.ofFintype (Bool × Bool)

private abbrev e1FirstBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.fst⟩

private abbrev e1SecondBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel Prod.snd⟩

private abbrev e1IdentityBundle : PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel id⟩

private abbrev e1Unit (bundle : PrimitiveBundle (Bool × Bool)) :
    TheoremUnit e1Arena where
  primitives := bundle
  Statement := True
  proof := True.intro

private abbrev e1Catalog : Catalog e1Arena :=
  Catalog.ofVector fun index : Fin 3 =>
    if index = 0 then e1Unit e1FirstBundle
    else if index = 1 then e1Unit e1SecondBundle
    else e1Unit e1IdentityBundle

private def e1KernelClasses : Finset e1Catalog.GeneratedKernel :=
  (Finset.univ : Finset (Finset (Fin 3))).image e1Catalog.generatedKernel

private theorem generatedKernel_insert_step
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (added : catalog.Index) :
    catalog.GeneratorStep
      (catalog.generatedKernel selected)
      (catalog.generatedKernel (insert added selected)) added := by
  refine ⟨selected, rfl, rfl, ?_⟩
  intro left right related
  exact catalog.indistinguishable_mono
    (Finset.subset_insert added selected) related

private theorem e1_empty_first_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel ∅) (e1Catalog.generatedKernel {0}) 0 := by
  refine ⟨generatedKernel_insert_step e1Catalog ∅ 0, ?_⟩
  change ¬e1Catalog.generatedKernel ∅ ≤ e1Catalog.generatedKernel {0}
  decide

private theorem e1_empty_second_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel ∅) (e1Catalog.generatedKernel {1}) 1 := by
  refine ⟨generatedKernel_insert_step e1Catalog ∅ 1, ?_⟩
  change ¬e1Catalog.generatedKernel ∅ ≤ e1Catalog.generatedKernel {1}
  decide

private theorem e1_first_full_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel {0}) (e1Catalog.generatedKernel {0, 1}) 1 := by
  have step := generatedKernel_insert_step e1Catalog {0} 1
  have inserted : insert 1 ({0} : Finset (Fin 3)) = {0, 1} := by
    ext index
    simp [or_comm]
  rw [inserted] at step
  exact ⟨step, by
    change ¬e1Catalog.generatedKernel {0} ≤ e1Catalog.generatedKernel {0, 1}
    decide⟩

private theorem e1_second_full_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel {1}) (e1Catalog.generatedKernel {0, 1}) 0 := by
  exact ⟨generatedKernel_insert_step e1Catalog {1} 0, by
    change ¬e1Catalog.generatedKernel {1} ≤ e1Catalog.generatedKernel {0, 1}
    decide⟩

private theorem e1_empty_identity_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel ∅) (e1Catalog.generatedKernel {2}) 2 := by
  refine ⟨generatedKernel_insert_step e1Catalog ∅ 2, ?_⟩
  change ¬e1Catalog.generatedKernel ∅ ≤ e1Catalog.generatedKernel {2}
  decide

private theorem e1_coordinate_full_eq :
    e1Catalog.generatedKernel {0, 1} =
      e1Catalog.generatedKernel e1Catalog.fullIndexSet := by
  decide

private theorem e1_identity_full_eq :
    e1Catalog.generatedKernel {2} =
      e1Catalog.generatedKernel e1Catalog.fullIndexSet := by
  decide

private theorem e1_first_catalog_full_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel {0})
      (e1Catalog.generatedKernel e1Catalog.fullIndexSet) 1 := by
  rw [← e1_coordinate_full_eq]
  exact e1_first_full_strict

private theorem e1_second_catalog_full_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel {1})
      (e1Catalog.generatedKernel e1Catalog.fullIndexSet) 0 := by
  rw [← e1_coordinate_full_eq]
  exact e1_second_full_strict

private theorem e1_empty_catalog_full_identity_strict :
    e1Catalog.StrictGeneratorStep
      (e1Catalog.generatedKernel ∅)
      (e1Catalog.generatedKernel e1Catalog.fullIndexSet) 2 := by
  rw [← e1_identity_full_eq]
  exact e1_empty_identity_strict

private theorem e1_full_identity_collapsed :
    e1Catalog.CollapsedAddition (e1Catalog.generatedKernel {0, 1}) 2 := by
  refine ⟨{0, 1}, rfl, ?_, le_rfl⟩
  decide

private theorem e1_identity_first_collapsed :
    e1Catalog.CollapsedAddition (e1Catalog.generatedKernel {2}) 0 := by
  refine ⟨{2}, rfl, ?_, le_rfl⟩
  decide

private theorem e1_identity_second_collapsed :
    e1Catalog.CollapsedAddition (e1Catalog.generatedKernel {2}) 1 := by
  refine ⟨{2}, rfl, ?_, le_rfl⟩
  decide

/-- T-033: the E1 generator quotient has four kernel classes with escape
counts 12, 4, 4, and 0. -/
theorem e1_four_node_escape_counts :
    e1KernelClasses.card = 4 ∧
      (e1Catalog.generatedKernel ∅).escapeAt.card = 12 ∧
      (e1Catalog.generatedKernel {0}).escapeAt.card = 4 ∧
      (e1Catalog.generatedKernel {1}).escapeAt.card = 4 ∧
      (e1Catalog.generatedKernel {2}).escapeAt.card = 0 := by
  decide

/-- T-033: the coordinate nodes are incomparable and their two strict
decomposition paths form a diamond alongside the direct identity shortcut. -/
theorem e1_diamond_strict_steps :
    ¬e1Catalog.generatedKernel {0} ≤ e1Catalog.generatedKernel {1} ∧
      ¬e1Catalog.generatedKernel {1} ≤ e1Catalog.generatedKernel {0} ∧
      e1Catalog.StrictGeneratorStep
        (e1Catalog.generatedKernel ∅) (e1Catalog.generatedKernel {0}) 0 ∧
      e1Catalog.StrictGeneratorStep
        (e1Catalog.generatedKernel {0})
          (e1Catalog.generatedKernel e1Catalog.fullIndexSet) 1 ∧
      e1Catalog.StrictGeneratorStep
        (e1Catalog.generatedKernel ∅) (e1Catalog.generatedKernel {1}) 1 ∧
      e1Catalog.StrictGeneratorStep
        (e1Catalog.generatedKernel {1})
          (e1Catalog.generatedKernel e1Catalog.fullIndexSet) 0 ∧
      e1Catalog.StrictGeneratorStep
        (e1Catalog.generatedKernel ∅)
          (e1Catalog.generatedKernel e1Catalog.fullIndexSet) 2 := by
  exact ⟨by decide, by decide, e1_empty_first_strict, e1_first_catalog_full_strict,
    e1_empty_second_strict, e1_second_catalog_full_strict,
    e1_empty_catalog_full_identity_strict⟩

private def e1CoordinateSchedule : GeneratorSchedule e1Catalog where
  length := 3
  added := ![0, 1, 2]
  added_bijective := by decide
  node := ![
    e1Catalog.generatedKernel ∅,
    e1Catalog.generatedKernel {0},
    e1Catalog.generatedKernel {0, 1},
    e1Catalog.generatedKernel {0, 1}]
  starts_at_top := rfl
  ends_at_bottom := by decide
  classification index := by
    refine Fin.cases (.strict e1_empty_first_strict) (fun tail => ?_) index
    refine Fin.cases (.strict e1_first_full_strict) (fun tail => ?_) tail
    exact Fin.cases (.collapsed rfl e1_full_identity_collapsed)
      (fun impossible => Fin.elim0 impossible) tail

private def e1IdentitySchedule : GeneratorSchedule e1Catalog where
  length := 3
  added := ![2, 0, 1]
  added_bijective := by decide
  node := ![
    e1Catalog.generatedKernel ∅,
    e1Catalog.generatedKernel {2},
    e1Catalog.generatedKernel {2},
    e1Catalog.generatedKernel {2}]
  starts_at_top := rfl
  ends_at_bottom := by decide
  classification index := by
    refine Fin.cases (.strict e1_empty_identity_strict) (fun tail => ?_) index
    refine Fin.cases (.collapsed rfl e1_identity_first_collapsed) (fun tail => ?_) tail
    exact Fin.cases (.collapsed rfl e1_identity_second_collapsed)
      (fun impossible => Fin.elim0 impossible) tail

/-- T-033: the coordinate-first and identity-first schedules have increments
`(8, 4, 0)` and `(12, 0, 0)` respectively. -/
theorem e1_schedule_increment_counts :
    (fun index => e1CoordinateSchedule.incrementCount index) = ![8, 4, 0] ∧
      (fun index => e1IdentitySchedule.incrementCount index) = ![12, 0, 0] := by
  constructor <;> funext index <;> fin_cases index <;> decide

/-- T-033: every E1 occurrence has empty flat unique capture and the
multiplicity spectrum is `(0, 0, 8, 4)`. -/
theorem e1_unique_capture_and_spectrum :
    e1Catalog.uniqueCapturePairs 0 = ∅ ∧
      e1Catalog.uniqueCapturePairs 1 = ∅ ∧
      e1Catalog.uniqueCapturePairs 2 = ∅ ∧
      e1Catalog.captureSpectrum 0 = 0 ∧
      e1Catalog.captureSpectrum 1 = 0 ∧
      e1Catalog.captureSpectrum 2 = 8 ∧
      e1Catalog.captureSpectrum 3 = 4 := by
  decide

end D5.S3.ConceptDynamics.InformationEscape
