import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture

namespace LeanInformationAudit

open D5.S3.ConceptDynamics.InformationEscape

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

instance projectionEquivalentDecidable {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (a b : catalog.Index) :
    Decidable (catalog.KernelEquivalent a b) :=
  inferInstanceAs (Decidable (catalog.KernelRefines a b ∧ catalog.KernelRefines b a))

instance projectionRedundantDecidable {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) : Decidable (catalog.CatalogRedundant) :=
  inferInstanceAs (Decidable (∃ i, catalog.uniqueCaptureCount i = 0))

instance projectionNodeLE {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (a b : catalog.GeneratedKernel) : Decidable (a ≤ b) :=
  show Decidable (∀ x y, a.relation x y → b.relation x y) from inferInstance

instance projectionNodeLT {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (a b : catalog.GeneratedKernel) : Decidable (a < b) :=
  show Decidable (a ≤ b ∧ ¬b ≤ a) from inferInstance

/-- Test all single-generator intersections, without enumerating generated subsets. -/
def projectionCover {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (target : catalog.GeneratedKernel) : Prop :=
  target < catalog.generatedKernel selected ∧ ∀ added : catalog.Index,
    target ≤ catalog.generatedKernel (insert added selected) →
      catalog.generatedKernel (insert added selected) = target ∨
        catalog.generatedKernel (insert added selected) = catalog.generatedKernel selected

instance projectionCoverDecidable {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (selected : Finset catalog.Index)
    (target : catalog.GeneratedKernel) : Decidable (projectionCover catalog selected target) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ : catalog.Index, _))

private theorem insertion_le {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (added : catalog.Index) :
    catalog.generatedKernel (insert added selected) ≤ catalog.generatedKernel selected := by
  intro x y related
  exact catalog.indistinguishable_mono (Finset.subset_insert added selected) related

/-- The bounded generator test certifies covers in the entire extensional lattice. -/
theorem projection_cover_iff {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (target : catalog.GeneratedKernel) :
    projectionCover catalog selected target ↔
      Catalog.GeneratedKernel.IsCover target (catalog.generatedKernel selected) := by
  rw [Catalog.GeneratedKernel.IsCover, covBy_iff_lt_and_eq_or_eq]
  constructor
  · rintro ⟨strict, test⟩
    refine ⟨strict, ?_⟩
    intro middle lower upper
    induction middle using Quotient.inductionOn with
    | _ generators =>
      by_cases same : catalog.generatedKernel generators = catalog.generatedKernel selected
      · exact Or.inr same
      · left
        have existsSplit : ∃ added ∈ generators,
            catalog.generatedKernel (insert added selected) ≠ catalog.generatedKernel selected := by
          by_contra noSplit
          push Not at noSplit
          apply same
          apply le_antisymm upper
          intro x y related
          apply (catalog.indistinguishable_iff_forall generators x y).2
          intro added member
          have inserted : (catalog.generatedKernel (insert added selected)).relation x y := by
            rw [noSplit added member]
            exact related
          exact (catalog.indistinguishable_iff_forall _ x y).1 inserted added
            (Finset.mem_insert_self _ _)
        obtain ⟨added, member, split⟩ := existsSplit
        have middleLe : catalog.generatedKernel generators ≤
            catalog.generatedKernel (insert added selected) := by
          intro x y related
          apply (catalog.indistinguishable_insert_iff selected added x y).2
          exact ⟨(catalog.indistinguishable_iff_forall generators x y).1 related added member,
            upper x y related⟩
        rcases test added (le_trans lower middleLe) with equal | equal
        · exact le_antisymm (equal ▸ middleLe) lower
        · exact False.elim (split equal)
  · rintro ⟨strict, test⟩
    exact ⟨strict, fun added lower => test _ lower (insertion_le catalog selected added)⟩

/-- Reflected single additions build the engine's generator-step proof. -/
theorem projection_generator_step {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (selected : Finset catalog.Index) (added : catalog.Index) :
    catalog.GeneratorStep (catalog.generatedKernel selected)
      (catalog.generatedKernel (insert added selected)) added :=
  ⟨selected, rfl, rfl, insertion_le catalog selected added⟩

def projectionSelection {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {n : Nat} (order : Fin n → catalog.Index) (position : Nat) : Finset catalog.Index :=
  (Finset.univ.filter (fun index : Fin n => index.val < position)).image order

private theorem projectionSelection_succ {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) {n : Nat} (order : Fin n → catalog.Index)
    (position : Fin n) :
    projectionSelection catalog order (position.val + 1) =
      insert (order position) (projectionSelection catalog order position.val) := by
  ext index
  simp only [projectionSelection, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨j, before, rfl⟩
    by_cases same : j = position
    · exact Or.inl (congrArg order same)
    · right
      exact ⟨j, by have different := mt Fin.ext same; omega, rfl⟩
  · rintro (same | ⟨j, before, same⟩)
    · exact ⟨position, Nat.lt_succ_self _, same.symm⟩
    · exact ⟨j, by omega, same⟩

/-- A complete ordering produces the engine's certified schedule, including stutters. -/
def projectionSchedule {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {n : Nat} (order : Fin n → catalog.Index) (bijective : Function.Bijective order) :
    GeneratorSchedule catalog where
  length := n
  added := order
  added_bijective := bijective
  node := fun position => catalog.generatedKernel
    (projectionSelection catalog order position.val)
  starts_at_top := by simp [projectionSelection]
  ends_at_bottom := by
    congr 1
    ext index
    simp only [projectionSelection, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Catalog.fullIndexSet]
    exact ⟨fun _ => True.intro, fun _ => by
      obtain ⟨j, rfl⟩ := bijective.surjective index
      exact ⟨j, j.isLt, rfl⟩⟩
  classification := fun position => by
    let selected := projectionSelection catalog order position.val
    have step := projection_generator_step catalog selected (order position)
    have next := projectionSelection_succ catalog order position
    change GeneratorStepClass catalog (catalog.generatedKernel selected)
      (catalog.generatedKernel (projectionSelection catalog order (position.val + 1)))
      (order position)
    rw [next]
    by_cases same : catalog.generatedKernel selected =
        catalog.generatedKernel (insert (order position) selected)
    · exact .collapsed same (same ▸ step)
    · apply GeneratorStepClass.strict
      refine ⟨step, ?_⟩
      intro reverse
      exact same (le_antisymm reverse (insertion_le catalog selected (order position)))

/-- Reuse the catalog analysis laws for the materialized generated relations. -/
def projectionNodeCatalog {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {n : Nat} (selections : Fin n → Finset catalog.Index) : Catalog arena :=
  Catalog.ofVector fun index => {
    primitives := {
      Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      atom := fun _ => ⟨.cut, catalog.generatedKernelRelation (selections index)⟩ }
    Statement := True
    proof := True.intro }

/-- A complete projection represents every extensional generated relation. -/
def projectionComplete {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    {n : Nat} (selections : Fin n → Finset catalog.Index) : Prop :=
  ∀ selected : Finset catalog.Index, ∃ i, catalog.generatedKernel selected =
    catalog.generatedKernel (selections i)

instance projectionCompleteDecidable {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) {n : Nat}
    (selections : Fin n → Finset catalog.Index) : Decidable (projectionComplete catalog selections) :=
  inferInstanceAs (Decidable (∀ _ : Finset catalog.Index, ∃ _ : Fin n, _))

def projectionSuite {n : Nat} (root : Lean.Name)
    (catalogs : Fin n → PackedCatalog.{u, v, w}) : DesignatedRootCatalogSuite where
  rootId := root
  CatalogIndex := Fin n
  catalogIndexFintype := inferInstance
  catalogIndexDecidableEq := inferInstance
  catalogAt := catalogs

instance projectionSystemDecidable {n : Nat} (root : Lean.Name)
    (catalogs : Fin n → PackedCatalog.{u, v, w}) :
    Decidable (SystemCatalogIrredundant (projectionSuite root catalogs)) :=
  inferInstanceAs (Decidable (∀ i : Fin n, CatalogIrredundant (catalogs i).catalog))

end LeanInformationAudit
