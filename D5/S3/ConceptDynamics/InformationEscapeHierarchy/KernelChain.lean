/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classified generator schedules compress to strict paths with disjoint telescoping increments. -/

import D5.S3.ConceptDynamics.InformationEscapeHierarchy.GeneratedKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

/- Library-search audit trail (2026-09-05):
   * Repository searches for classified generator schedules, strict kernel
     subsequences, and telescoping escape chains found no existing owner.
   * Exact current-tree hits `Catalog.escape_antitone_on_step`,
     `escapeAt_generatedKernel_eq_escapePairs`, and
     `uniqueCapturePairs_eq_sdiff` provide the semantic step and terminal bridge.
   * Pinned Mathlib exact hits `Fin.antitone_iff_succ_le`, `Fin.sum_univ_succ`,
     `Finset.sdiff_union_sdiff_cancel`, and
     `Finset.card_sdiff_add_card_eq_card` provide the finite chain algebra.
   * No library declaration compresses a dependently classified Fin-indexed
     path, so the private `StrictPath` recursion below supplies that witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT
open scoped BigOperators

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

/-- A schedule step is either a strict generator edge or a certified stutter. -/
inductive GeneratorStepClass {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (source target : catalog.GeneratedKernel) (added : catalog.Index) where
  | strict (proof : catalog.StrictGeneratorStep source target added)
  | collapsed
      (same : source = target)
      (proof : catalog.CollapsedAddition source added)

/-- A complete catalog ordering whose equality steps remain explicitly classified. -/
structure GeneratorSchedule {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) where
  length : Nat
  added : Fin length → catalog.Index
  added_bijective : Function.Bijective added
  node : Fin (length + 1) → catalog.GeneratedKernel
  starts_at_top : node 0 = catalog.generatedKernel ∅
  ends_at_bottom :
    node ⟨length, Nat.lt_succ_self length⟩ =
      catalog.generatedKernel catalog.fullIndexSet
  classification : ∀ r : Fin length,
    GeneratorStepClass catalog (node r.castSucc) (node r.succ) (added r)

/-- A stutter-free generated-kernel path, with every adjacency certified strict. -/
structure StrictKernelChain {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) where
  length : Nat
  added : Fin length → catalog.Index
  node : Fin (length + 1) → catalog.GeneratedKernel
  step : ∀ r : Fin length,
    catalog.StrictGeneratorStep (node r.castSucc) (node r.succ) (added r)

private inductive StrictPath {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    catalog.GeneratedKernel → catalog.GeneratedKernel → Type (max u v w) where
  | nil (node : catalog.GeneratedKernel) : StrictPath catalog node node
  | cons {source middle target : catalog.GeneratedKernel}
      (added : catalog.Index)
      (step : catalog.StrictGeneratorStep source middle added)
      (tail : StrictPath catalog middle target) : StrictPath catalog source target

private def StrictPath.length
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} : StrictPath catalog source target → Nat
  | .nil _ => 0
  | .cons _ _ tail => tail.length + 1

private def StrictPath.added
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} (path : StrictPath catalog source target) :
    Fin path.length → catalog.Index :=
  match path with
  | .nil _ => Fin.elim0
  | .cons added _ tail => Fin.cases added tail.added

private def StrictPath.node
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} (path : StrictPath catalog source target) :
    Fin (path.length + 1) → catalog.GeneratedKernel :=
  match path with
  | .nil node => fun _ => node
  | .cons _ _ tail => Fin.cases source tail.node

@[simp] private theorem StrictPath.node_zero
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} (path : StrictPath catalog source target) :
    path.node 0 = source := by
  cases path <;> rfl

private theorem StrictPath.step
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} (path : StrictPath catalog source target) :
    ∀ r : Fin path.length,
      catalog.StrictGeneratorStep (path.node r.castSucc) (path.node r.succ) (path.added r) := by
  induction path with
  | nil node => exact fun r => Fin.elim0 r
  | @cons source middle target added firstStep tail inductionHypothesis =>
      intro r
      refine Fin.cases ?_ (fun j => ?_) r
      · change catalog.StrictGeneratorStep source (tail.node 0) added
        rw [tail.node_zero]
        exact firstStep
      · change catalog.StrictGeneratorStep
          (tail.node j.castSucc) (tail.node j.succ) (tail.added j)
        exact inductionHypothesis j

private def StrictPath.toChain
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {source target : catalog.GeneratedKernel} (path : StrictPath catalog source target) :
    StrictKernelChain catalog where
  length := path.length
  added := path.added
  node := path.node
  step := path.step

private noncomputable def classifiedPath
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (n : Nat) (added : Fin n → catalog.Index)
    (node : Fin (n + 1) → catalog.GeneratedKernel)
    (classification : ∀ r : Fin n,
      GeneratorStepClass catalog (node r.castSucc) (node r.succ) (added r)) :
    StrictPath catalog (node 0) (node ⟨n, Nat.lt_succ_self n⟩) := by
  induction n with
  | zero =>
      exact .nil (node 0)
  | succ n inductionHypothesis =>
      let tailAdded : Fin n → catalog.Index := fun r => added r.succ
      let tailNode : Fin (n + 1) → catalog.GeneratedKernel := fun r => node r.succ
      have tailClassification : ∀ r : Fin n,
          GeneratorStepClass catalog
            (tailNode r.castSucc) (tailNode r.succ) (tailAdded r) := by
        intro r
        have classified := classification r.succ
        change GeneratorStepClass catalog
          (node r.castSucc.succ) (node r.succ.succ) (added r.succ)
        rw [show r.castSucc.succ = r.succ.castSucc by apply Fin.ext; rfl]
        exact classified
      have tailPath := inductionHypothesis tailAdded tailNode tailClassification
      have firstClass := classification (0 : Fin (n + 1))
      cases firstClass with
      | strict proof =>
          apply StrictPath.cons (added 0) proof
          convert tailPath using 1 <;> apply congrArg node <;> apply Fin.ext <;> rfl
      | collapsed same proof =>
          have same' : node 0 = node (Fin.succ 0) := by
            convert same using 1 <;> apply congrArg node <;> apply Fin.ext <;> rfl
          rw [same']
          convert tailPath using 1 <;> apply congrArg node <;> apply Fin.ext <;> rfl

namespace GeneratorSchedule

/-- Delete classified stutters while retaining every strict schedule edge in order. -/
noncomputable def strictSubsequence
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) : StrictKernelChain catalog :=
  (classifiedPath catalog schedule.length schedule.added schedule.node
    schedule.classification).toChain

/-- Escape pairs captured by one classified schedule step. -/
def increment {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (r : Fin schedule.length) :
    Finset (arena.State × arena.State) :=
  (schedule.node r.castSucc).edgeCapture (schedule.node r.succ)

/-- Number of escape pairs captured by one classified schedule step. -/
def incrementCount {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (r : Fin schedule.length) : Nat :=
  (schedule.increment r).card

end GeneratorSchedule

namespace StrictKernelChain

/-- Escape pairs captured by one strict-chain edge. -/
def increment {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (chain : StrictKernelChain catalog) (r : Fin chain.length) :
    Finset (arena.State × arena.State) :=
  (chain.node r.castSucc).edgeCapture (chain.node r.succ)

/-- Number of escape pairs captured by one strict-chain edge. -/
def incrementCount {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (chain : StrictKernelChain catalog) (r : Fin chain.length) : Nat :=
  (chain.increment r).card

end StrictKernelChain

private theorem schedule_step_escape_subset
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (r : Fin schedule.length) :
    (schedule.node r.succ).escapeAt ⊆ (schedule.node r.castSucc).escapeAt := by
  cases schedule.classification r with
  | strict proof => exact catalog.escape_antitone_on_step proof.1
  | collapsed same proof =>
      rw [same]

private theorem schedule_escape_antitone
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) :
    Antitone (fun r : Fin (schedule.length + 1) => (schedule.node r).escapeAt) :=
  Fin.antitone_iff_succ_le.mpr (schedule_step_escape_subset schedule)

/-- A classified collapsed step has empty increment and contributes zero pairs. -/
theorem collapsed_increment_eq_empty
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (r : Fin schedule.length)
    (same : schedule.node r.castSucc = schedule.node r.succ) :
    schedule.increment r = ∅ := by
  simp [GeneratorSchedule.increment, Catalog.GeneratedKernel.edgeCapture, same]

private theorem increments_disjoint_of_lt
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) {r s : Fin schedule.length} (less : r < s) :
    Disjoint (schedule.increment r) (schedule.increment s) := by
  apply Finset.disjoint_left.mpr
  intro pair inFirst inSecond
  have firstParts := Finset.mem_sdiff.mp inFirst
  have secondParts := Finset.mem_sdiff.mp inSecond
  apply firstParts.2
  apply schedule_escape_antitone schedule
    (show r.succ ≤ s.castSucc by simpa using less)
  exact secondParts.1

/-- IE-045: increments at distinct schedule positions are pairwise disjoint. -/
theorem chain_increment_pairwise_disjoint
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) :
    ∀ r s : Fin schedule.length, r ≠ s →
      Disjoint (schedule.increment r) (schedule.increment s) := by
  intro r s different
  rcases lt_or_gt_of_ne different with less | greater
  · exact increments_disjoint_of_lt schedule less
  · exact (increments_disjoint_of_lt schedule greater).symm

private theorem exists_membership_boundary
    {alpha : Type u} {n : Nat} (sets : Fin (n + 1) → Finset alpha)
    [DecidableEq alpha] (element : alpha)
    (atStart : element ∈ sets 0)
    (notAtEnd : element ∉ sets ⟨n, Nat.lt_succ_self n⟩) :
    ∃ r : Fin n, element ∈ sets r.castSucc ∧ element ∉ sets r.succ := by
  induction n with
  | zero =>
      exfalso
      exact notAtEnd (by simpa using atStart)
  | succ n inductionHypothesis =>
      by_cases atNext : element ∈ sets (Fin.succ 0)
      · let tailSets : Fin (n + 1) → Finset alpha := fun r => sets r.succ
        have tailNotAtEnd : element ∉ tailSets ⟨n, Nat.lt_succ_self n⟩ := by
          change element ∉ sets (Fin.succ ⟨n, Nat.lt_succ_self n⟩)
          rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ =
              (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) by
            apply Fin.ext
            rfl]
          exact notAtEnd
        obtain ⟨r, atLeft, notAtRight⟩ :=
          inductionHypothesis tailSets atNext tailNotAtEnd
        refine ⟨r.succ, ?_, ?_⟩
        · change element ∈ sets r.succ.castSucc
          change element ∈ sets r.castSucc.succ at atLeft
          rw [show r.succ.castSucc = r.castSucc.succ by apply Fin.ext; rfl]
          exact atLeft
        · change element ∉ sets r.succ.succ
          change element ∉ sets r.succ.succ at notAtRight
          exact notAtRight
      · exact ⟨0, by simpa using atStart, by simpa using atNext⟩

/-- IE-046: the union of all schedule increments is exactly the terminal escape loss. -/
theorem chain_increment_union
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) :
    Finset.univ.biUnion schedule.increment =
      (schedule.node 0).escapeAt \
        (schedule.node ⟨schedule.length, Nat.lt_succ_self schedule.length⟩).escapeAt := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  ext pair
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨r, inIncrement⟩
    have parts := Finset.mem_sdiff.mp inIncrement
    refine ⟨schedule_escape_antitone schedule (Fin.zero_le r.castSucc) parts.1, ?_⟩
    intro atEnd
    exact parts.2 (schedule_escape_antitone schedule (Fin.le_last r.succ) atEnd)
  · rintro ⟨atStart, notAtEnd⟩
    obtain ⟨r, atLeft, notAtRight⟩ :=
      exists_membership_boundary
        (fun j => (schedule.node j).escapeAt) pair atStart notAtEnd
    exact ⟨r, Finset.mem_sdiff.mpr ⟨atLeft, notAtRight⟩⟩

private theorem sum_sdiff_card_add_last
    {alpha : Type u} [DecidableEq alpha] {n : Nat}
    (sets : Fin (n + 1) → Finset alpha)
    (antitone : Antitone sets) :
    (∑ r : Fin n, (sets r.castSucc \ sets r.succ).card) +
        (sets ⟨n, Nat.lt_succ_self n⟩).card = (sets 0).card := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      let tailSets : Fin (n + 1) → Finset alpha := fun r => sets r.succ
      have tailAntitone : Antitone tailSets := fun _ _ less =>
        antitone (Fin.succ_le_succ_iff.mpr less)
      have tailIdentity := inductionHypothesis tailSets tailAntitone
      have firstSubset : sets (Fin.succ 0) ⊆ sets 0 := antitone (Fin.zero_le _)
      rw [Fin.sum_univ_succ]
      have crossIndex (r : Fin n) : r.succ.castSucc = r.castSucc.succ := Fin.ext rfl
      have lastIndex :
          (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) =
            (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ := Fin.ext rfl
      have tailIdentity' :
          (∑ r : Fin n, (sets r.succ.castSucc \ sets r.succ.succ).card) +
              (sets ⟨n + 1, Nat.lt_succ_self (n + 1)⟩).card =
            (sets (Fin.succ 0)).card := by
        simp_rw [crossIndex, lastIndex]
        simpa only [tailSets] using tailIdentity
      simp_rw [crossIndex, lastIndex]
      calc
        (sets (0 : Fin (n + 2)) \ sets (Fin.succ 0)).card +
              (∑ r : Fin n, (sets r.succ.castSucc \ sets r.succ.succ).card) +
              (sets ⟨n + 1, Nat.lt_succ_self (n + 1)⟩).card =
            (sets (0 : Fin (n + 2)) \ sets (Fin.succ 0)).card +
              (sets (Fin.succ 0)).card := by
                simpa only [add_assoc] using
                  congrArg
                    (fun value =>
                      (sets (0 : Fin (n + 2)) \ sets (Fin.succ 0)).card + value)
                    tailIdentity'
        _ = (sets 0).card := Finset.card_sdiff_add_card_eq_card firstSubset

/-- IE-047: increment counts telescope additively without natural subtraction. -/
theorem chain_count_telescopes
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) :
    (∑ r : Fin schedule.length, schedule.incrementCount r) +
        ((schedule.node ⟨schedule.length,
          Nat.lt_succ_self schedule.length⟩).escapeAt).card =
      ((schedule.node 0).escapeAt).card := by
  exact sum_sdiff_card_add_last
    (fun r => (schedule.node r).escapeAt) (schedule_escape_antitone schedule)

private theorem strict_path_terminal_eq_generatedKernel_union
    {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (n : Nat) (added : Fin n → catalog.Index)
    (node : Fin (n + 1) → catalog.GeneratedKernel)
    (steps : ∀ r : Fin n,
      catalog.StrictGeneratorStep (node r.castSucc) (node r.succ) (added r))
    (selected : Finset catalog.Index)
    (starts : catalog.generatedKernel selected = node 0) :
    catalog.generatedKernel (by
      letI := catalog.indexDecidableEq
      exact selected ∪ Finset.univ.image added) =
        node ⟨n, Nat.lt_succ_self n⟩ := by
  induction n generalizing selected with
  | zero =>
      simpa using starts
  | succ n inductionHypothesis =>
      let tailAdded : Fin n → catalog.Index := fun r => added r.succ
      let tailNode : Fin (n + 1) → catalog.GeneratedKernel := fun r => node r.succ
      have tailSteps : ∀ r : Fin n,
          catalog.StrictGeneratorStep
            (tailNode r.castSucc) (tailNode r.succ) (tailAdded r) := by
        intro r
        change catalog.StrictGeneratorStep
          (node r.castSucc.succ) (node r.succ.succ) (added r.succ)
        rw [show r.castSucc.succ = r.succ.castSucc by apply Fin.ext; rfl]
        exact steps r.succ
      rcases (steps (0 : Fin (n + 1))).1 with
        ⟨representative, representativeStart, representativeNext, refinement⟩
      have sameStart :
          catalog.generatedKernel selected =
            catalog.generatedKernel representative :=
        starts.trans (by
          rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by
            apply Fin.ext
            rfl]
          exact representativeStart.symm)
      have tailStarts :
          catalog.generatedKernel (insert (added 0) selected) = tailNode 0 := by
        rw [catalog.generatorStep_wellDefined (added 0) sameStart]
        change catalog.generatedKernel (insert (added 0) representative) =
          node (Fin.succ 0)
        exact representativeNext
      have tailResult := inductionHypothesis tailAdded tailNode tailSteps
        (insert (added 0) selected) tailStarts
      have imageDecomposition :
          Finset.univ.image added =
            insert (added 0) (Finset.univ.image tailAdded) := by
        ext index
        simp only [Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · rintro ⟨position, rfl⟩
          refine Fin.cases (Or.inl rfl) (fun r => Or.inr ?_) position
          exact ⟨r, rfl⟩
        · rintro (same | ⟨position, same⟩)
          · exact ⟨0, same.symm⟩
          · exact ⟨position.succ, same⟩
      rw [imageDecomposition]
      have unionIdentity :
          selected ∪ insert (added 0) (Finset.univ.image tailAdded) =
            insert (added 0) selected ∪ Finset.univ.image tailAdded := by
        ext index
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [unionIdentity]
      rw [tailResult]
      apply congrArg node
      apply Fin.ext
      rfl

/-- A strict chain ends at the kernel generated by its start and all retained labels. -/
theorem strict_chain_terminal_eq_generatedKernel_union
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (chain : StrictKernelChain catalog) (selected : Finset catalog.Index)
    (starts : chain.node 0 = catalog.generatedKernel selected) :
    chain.node ⟨chain.length, Nat.lt_succ_self chain.length⟩ =
      catalog.generatedKernel (by
        letI := catalog.indexDecidableEq
        exact selected ∪ Finset.univ.image chain.added) := by
  exact (strict_path_terminal_eq_generatedKernel_union catalog chain.length
    chain.added chain.node chain.step selected starts.symm).symm

/-- IE-048: strict chains with one start and generator set have one extensional terminal. -/
theorem terminal_order_independent
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : StrictKernelChain catalog) (selected : Finset catalog.Index)
    (firstStarts : first.node 0 = catalog.generatedKernel selected)
    (secondStarts : second.node 0 = catalog.generatedKernel selected)
    (sameGenerators : Finset.univ.image first.added = Finset.univ.image second.added) :
    first.node ⟨first.length, Nat.lt_succ_self first.length⟩ =
      second.node ⟨second.length, Nat.lt_succ_self second.length⟩ := by
  rw [strict_chain_terminal_eq_generatedKernel_union first selected firstStarts,
    strict_chain_terminal_eq_generatedKernel_union second selected secondStarts,
    sameGenerators]

/-- Every full generator schedule terminates at the same extensional bottom node. -/
theorem full_schedule_terminal_order_independent
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (first second : GeneratorSchedule catalog) :
    first.node ⟨first.length, Nat.lt_succ_self first.length⟩ =
      second.node ⟨second.length, Nat.lt_succ_self second.length⟩ := by
  rw [first.ends_at_bottom, second.ends_at_bottom]

/-- Every full schedule endpoint is the kernel generated by the full catalog. -/
theorem schedule_terminal_eq_generatedKernel_full
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) :
    schedule.node ⟨schedule.length, Nat.lt_succ_self schedule.length⟩ =
      catalog.generatedKernel catalog.fullIndexSet :=
  schedule.ends_at_bottom

/-- IE-049: a certified leave-one-out penultimate node gives the unique last capture. -/
theorem last_step_eq_uniqueCapture
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (schedule : GeneratorSchedule catalog) (index : catalog.Index)
    (positive : 0 < schedule.length)
    (beforeLast :
      schedule.node ⟨schedule.length - 1,
        by omega⟩ =
          catalog.generatedKernel (catalog.without index))
    (lastAdded :
      schedule.added ⟨schedule.length - 1,
        by omega⟩ = index) :
    schedule.increment ⟨schedule.length - 1,
      by omega⟩ = catalog.uniqueCapturePairs index := by
  letI := arena.stateFintype
  letI := arena.stateDecidableEq
  let last : Fin schedule.length :=
    ⟨schedule.length - 1, by omega⟩
  have lastNode : schedule.node last.succ =
      catalog.generatedKernel catalog.fullIndexSet := by
    rw [show last.succ = ⟨schedule.length, Nat.lt_succ_self schedule.length⟩ by
      apply Fin.ext
      change schedule.length - 1 + 1 = schedule.length
      omega]
    exact schedule.ends_at_bottom
  have beforeLast' : schedule.node last.castSucc =
      catalog.generatedKernel (catalog.without index) := by
    rw [show last.castSucc =
        (⟨schedule.length - 1, by omega⟩ : Fin (schedule.length + 1)) by
      apply Fin.ext
      rfl]
    exact beforeLast
  rw [show (⟨schedule.length - 1,
      by omega⟩ : Fin schedule.length) = last by rfl]
  unfold GeneratorSchedule.increment Catalog.GeneratedKernel.edgeCapture
  rw [beforeLast', lastNode,
    Catalog.GeneratedKernel.escapeAt_generatedKernel_eq_escapePairs,
    Catalog.GeneratedKernel.escapeAt_generatedKernel_eq_escapePairs]
  exact (catalog.uniqueCapturePairs_eq_sdiff index).symm

end D5.S3.ConceptDynamics.InformationEscape
