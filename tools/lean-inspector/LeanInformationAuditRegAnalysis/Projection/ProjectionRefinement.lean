import D5.S3.ConceptDynamics.InformationEscapeHierarchy.GeneratedKernel

namespace LeanInformationAudit

open D5.S3.ConceptDynamics.InformationEscape

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

/-- Executable refinement scans the complete finite relation table. -/
def projectionRefinesB {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (a b : catalog.GeneratedKernel) : Bool :=
  Finset.fold (fun left right => left && right) true
    (fun pair => !a.relationB pair.1 pair.2 || b.relationB pair.1 pair.2)
    ((Finset.univ : Finset arena.State) ×ˢ Finset.univ)

theorem projectionRefinesB_eq_true_iff
    {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (a b : catalog.GeneratedKernel) : projectionRefinesB a b = true ↔ a ≤ b := by
  have pointwise : ∀ left right,
      (!a.relationB left right || b.relationB left right) = true ↔
        (a.relation left right → b.relation left right) := by
    intro left right
    rw [← a.relationB_eq_true_iff, ← b.relationB_eq_true_iff]
    cases a.relationB left right <;> cases b.relationB left right <;> decide
  have foldCharacterization :=
    Finset.fold_op_rel_iff_and
      (op := fun left right : Bool => left && right)
      (r := fun _ actual : Bool => actual = true)
      (b := true)
      (f := fun pair : arena.State × arena.State =>
        !a.relationB pair.1 pair.2 || b.relationB pair.1 pair.2)
      (s := (Finset.univ : Finset arena.State) ×ˢ Finset.univ)
      (c := true) (by
        intro expected left right
        simp)
  constructor
  · intro scan left right related
    have implication := (foldCharacterization.mp scan).2 (left, right) (by simp)
    exact (pointwise left right).mp implication related
  · intro refines
    apply foldCharacterization.mpr
    refine ⟨rfl, ?_⟩
    intro pair _
    exact (pointwise pair.1 pair.2).mpr (refines pair.1 pair.2)

instance projectionNodeLE {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    (a b : catalog.GeneratedKernel) : Decidable (a ≤ b) :=
  decidable_of_iff (projectionRefinesB a b = true) (projectionRefinesB_eq_true_iff a b)

abbrev ReflectedRefinementTable (n : Nat) := Fin n → Fin n → Bool

/-- The checker scans only the certified, reducible readout relations. -/
def reflectedRefinesChecker {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {n : Nat} (nodes : Fin n → catalog.GeneratedKernel)
    (table : ReflectedRefinementTable n) : Bool :=
  decide (∀ a b, table a b = projectionRefinesB (nodes a) (nodes b))

/-- Both directions are needed: strictness uses an inclusion and a reverse non-inclusion. -/
theorem reflectedRefines_sound {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {n : Nat} (nodes : Fin n → catalog.GeneratedKernel)
    (table : ReflectedRefinementTable n) (checked : reflectedRefinesChecker nodes table = true) :
    ∀ a b, table a b = true ↔ nodes a ≤ nodes b := by
  have cells : ∀ a b, table a b = projectionRefinesB (nodes a) (nodes b) :=
    of_decide_eq_true checked
  intro a b
  rw [cells a b, projectionRefinesB_eq_true_iff]

theorem reflectedStrict_sound {arena : Arena.{u}} {catalog : Catalog.{u, v, w} arena}
    {n : Nat} (nodes : Fin n → catalog.GeneratedKernel)
    (table : ReflectedRefinementTable n) (checked : reflectedRefinesChecker nodes table = true)
    (a b : Fin n) (forward : table a b = true) (reverse : table b a = false) :
    nodes a < nodes b := by
  rw [lt_iff_le_not_ge]
  refine ⟨(reflectedRefines_sound nodes table checked a b).mp forward, ?_⟩
  intro backward
  have positive := (reflectedRefines_sound nodes table checked b a).mpr backward
  rw [reverse] at positive
  contradiction

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

end LeanInformationAudit
