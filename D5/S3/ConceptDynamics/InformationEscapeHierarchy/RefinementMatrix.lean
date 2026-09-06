/- GID: D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ordered finite refinement search returns the first separating state pair. -/

import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.AnalysisLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Catalog

inductive KernelComparison
  | equal
  | strictlyFiner
  | strictlyCoarser
  | incomparable
  deriving DecidableEq, Repr

def kernelComparison {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : catalog.Index) :
    KernelComparison :=
  if catalog.KernelRefines left right then
    if catalog.KernelRefines right left then .equal else .strictlyFiner
  else if catalog.KernelRefines right left then .strictlyCoarser
  else .incomparable

private def separatesRefinement {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index)
    (pair : arena.State × arena.State) : Bool :=
  (catalog.theoremAt finer).primitives.agreesB pair.1 pair.2 &&
    !(catalog.theoremAt coarser).primitives.agreesB pair.1 pair.2

private theorem agreesB_eq_false_iff {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State) :
    bundle.agreesB left right = false ↔ ¬bundle.agrees left right := by
  constructor
  · intro booleanFalse agreement
    have booleanTrue := (bundle.agreesB_eq_true_iff left right).2 agreement
    simp [booleanFalse] at booleanTrue
  · intro disagreement
    cases booleanValue : bundle.agreesB left right
    · rfl
    · exact False.elim
        (disagreement ((bundle.agreesB_eq_true_iff left right).1 booleanValue))

private theorem separatesRefinement_eq_true_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (finer coarser : catalog.Index)
    (pair : arena.State × arena.State) :
    separatesRefinement catalog finer coarser pair = true ↔
      (catalog.theoremAt finer).primitives.agrees pair.1 pair.2 ∧
        ¬(catalog.theoremAt coarser).primitives.agrees pair.1 pair.2 := by
  simp [separatesRefinement, PrimitiveBundle.agreesB_eq_true_iff,
    agreesB_eq_false_iff]

/-- Spec spelling: `refinementWitness?`. The search visits pairs in the exact
outer-left, inner-right order of `enum.states.product enum.states`. -/
def refinementWitness {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (enum : Arena.StateEnumeration arena)
    (finer coarser : catalog.Index) : Option (arena.State × arena.State) :=
  (enum.states.product enum.states).find?
    (separatesRefinement catalog finer coarser)

/-- The selector is definitionally the first match in the documented pair order. -/
theorem refinementWitness_order {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (enum : Arena.StateEnumeration arena)
    (finer coarser : catalog.Index) :
    catalog.refinementWitness enum finer coarser =
      (enum.states.product enum.states).find?
        (separatesRefinement catalog finer coarser) := by
  rfl

theorem refinementWitness_eq_none_iff {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (enum : Arena.StateEnumeration arena)
    (finer coarser : catalog.Index) :
    catalog.refinementWitness enum finer coarser = none ↔
      catalog.KernelRefines finer coarser := by
  rw [refinementWitness, List.find?_eq_none]
  constructor
  · intro noWitness left right fineAgrees
    by_contra coarseSeparates
    have leftMem : left ∈ enum.states := by
      rw [← List.mem_toFinset, enum.complete]
      exact Finset.mem_univ left
    have rightMem : right ∈ enum.states := by
      rw [← List.mem_toFinset, enum.complete]
      exact Finset.mem_univ right
    have pairMem : (left, right) ∈ enum.states.product enum.states :=
      List.mem_product.mpr ⟨leftMem, rightMem⟩
    exact noWitness (left, right) pairMem
      ((separatesRefinement_eq_true_iff catalog finer coarser _).2
        ⟨fineAgrees, coarseSeparates⟩)
  · intro refines pair _
    rw [separatesRefinement_eq_true_iff]
    intro selected
    exact selected.2 (refines pair.1 pair.2 selected.1)

theorem refinementWitness_eq_some_implies {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (enum : Arena.StateEnumeration arena)
    (finer coarser : catalog.Index) (pair : arena.State × arena.State)
    (found : catalog.refinementWitness enum finer coarser = some pair) :
    (catalog.theoremAt finer).primitives.agrees pair.1 pair.2 ∧
      ¬(catalog.theoremAt coarser).primitives.agrees pair.1 pair.2 := by
  have selected := List.find?_some (show
    (enum.states.product enum.states).find?
      (separatesRefinement catalog finer coarser) = some pair from found)
  exact (separatesRefinement_eq_true_iff catalog finer coarser pair).1 selected

theorem refinementWitness_exists_iff_not_kernelRefines {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (enum : Arena.StateEnumeration arena)
    (finer coarser : catalog.Index) :
    (∃ pair, catalog.refinementWitness enum finer coarser = some pair) ↔
      ¬catalog.KernelRefines finer coarser := by
  rw [← not_congr (catalog.refinementWitness_eq_none_iff enum finer coarser)]
  cases catalog.refinementWitness enum finer coarser <;> simp

theorem kernelComparison_spec {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (enum : Arena.StateEnumeration arena)
    (left right : catalog.Index) :
    (catalog.kernelComparison left right = .equal ↔
      catalog.KernelRefines left right ∧ catalog.KernelRefines right left) ∧
    (catalog.kernelComparison left right = .strictlyFiner ↔
      catalog.KernelRefines left right ∧
        ∃ pair, catalog.refinementWitness enum right left = some pair) ∧
    (catalog.kernelComparison left right = .strictlyCoarser ↔
      (∃ pair, catalog.refinementWitness enum left right = some pair) ∧
        catalog.KernelRefines right left) ∧
    (catalog.kernelComparison left right = .incomparable ↔
      (∃ pair, catalog.refinementWitness enum left right = some pair) ∧
        ∃ pair, catalog.refinementWitness enum right left = some pair) := by
  unfold kernelComparison
  rw [catalog.refinementWitness_exists_iff_not_kernelRefines enum left right,
    catalog.refinementWitness_exists_iff_not_kernelRefines enum right left]
  by_cases forward : catalog.KernelRefines left right <;>
    by_cases reverse : catalog.KernelRefines right left <;> simp [forward, reverse]

private abbrev e1Arena : Arena := Arena.ofFintype (Bool × Bool)

private abbrev e1CoordinateUnit (readout : Bool × Bool -> Bool) :
    TheoremUnit e1Arena where
  primitives :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      atom := fun _ => ⟨.cut, cutKernel readout⟩ }
  Statement := True
  proof := trivial

private abbrev e1Catalog : Catalog e1Arena := Catalog.ofVector fun index : Fin 2 =>
  if index = 0 then e1CoordinateUnit Prod.fst else e1CoordinateUnit Prod.snd

private def e1Enumeration : Arena.StateEnumeration e1Arena where
  states := [(false, false), (false, true), (true, false), (true, true)]
  nodup := by decide
  complete := by decide

example : e1Catalog.refinementWitness e1Enumeration 0 1 =
    some ((false, false), (false, true)) := by rfl

example : e1Catalog.refinementWitness e1Enumeration 0 0 = none := by rfl

end Catalog

end D5.S3.ConceptDynamics.InformationEscape
