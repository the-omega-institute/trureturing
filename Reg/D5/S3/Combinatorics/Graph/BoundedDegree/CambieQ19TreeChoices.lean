import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices
import Reg.Support.SingleDependentReadout

/-! The configuration-order readout in the pointwise tree-fiber law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices

open _root_.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Configuration) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ c => c.vertexOrder) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : Configuration) (e : DeletionChoices c),
    Nat.card ((treeFiberEquiv c).symm e).val.verts = R.readout () () c

private def singletonConfig : Configuration := .firstOnly ⟨(0, 0), le_rfl⟩

private def twoVertexConfig : Configuration := .firstOnly ⟨(0, 1), by decide⟩

private theorem singletonCoreMissing : coreSet singletonConfig.vertices ≠ Set.univ := by
  intro h
  have hm : (0 : Fin 5000) ∈ coreSet singletonConfig.vertices := h.symm ▸ Set.mem_univ _
  exact (show False from hm)

private theorem singletonTriangleMissing : triangleSet singletonConfig.vertices ≠ Set.univ := by
  intro h
  have hm : (0 : Fin 3) ∈ triangleSet singletonConfig.vertices := h.symm ▸ Set.mem_univ _
  exact (show False from hm)

private def singletonChoice : DeletionChoices singletonConfig :=
  ⟨(properCycleChoiceEquiv _ singletonCoreMissing).symm (),
    (properCycleChoiceEquiv _ singletonTriangleMissing).symm ()⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h singletonConfig singletonChoice
  rw [treeFiberEquiv_order] at hs
  exact Nat.noConfusion (show (1 : ℕ) = 0 from hs)

def family : Registration arena (type_of% @treeFiberEquiv_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨treeFiberEquiv_order, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), singletonConfig, twoVertexConfig, by change (1 : ℕ) ≠ 2; decide⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@treeFiberEquiv_order) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.treeFiberEquiv_order.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c.vertexOrder) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration


open SimpleGraph
open scoped Sym2

private def fullTriangle : Configuration :=
  .triangleOnly ⟨Finset.univ, Finset.univ_nonempty⟩

private theorem fullTriangleCoreMissing : coreSet fullTriangle.vertices ≠ Set.univ := by
  intro h
  have hm : (0 : Fin 5000) ∈ coreSet fullTriangle.vertices := h.symm ▸ Set.mem_univ _
  exact (show False from hm)

private theorem fullTrianglePresent : triangleSet fullTriangle.vertices = Set.univ := by
  ext x
  change x ∈ (Finset.univ : Finset (Fin 3)) ↔ x ∈ Set.univ
  simp

namespace Cardinality

abbrev actual : Realization signature :=
  realize signature (fun _ _ c => Nat.card (DeletionChoices c)) (fun e => nomatch e)

abbrev arena : Arena := by
  classical
  exact {
    signature := signature
    Law R := ∀ c : Configuration,
      R.readout () () c =
        (if coreSet c.vertices = Set.univ then 5000 else 1) *
        (if triangleSet c.vertices = Set.univ then 3 else 1) }

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h singletonConfig
  change 0 = (if coreSet singletonConfig.vertices = Set.univ then 5000 else 1) *
    (if triangleSet singletonConfig.vertices = Set.univ then 3 else 1) at hs
  rw [ite_eq_right singletonCoreMissing, ite_eq_right singletonTriangleMissing] at hs
  exact Nat.noConfusion hs

def family : Registration arena (type_of% @deletionChoices_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨deletionChoices_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), singletonConfig, fullTriangle, ?_⟩
    change Nat.card (DeletionChoices singletonConfig) ≠ Nat.card (DeletionChoices fullTriangle)
    rw [deletionChoices_card singletonConfig, deletionChoices_card fullTriangle]
    rw [ite_eq_right singletonCoreMissing, ite_eq_right singletonTriangleMissing,
      ite_eq_right fullTriangleCoreMissing, ite_eq_left fullTrianglePresent]
    decide

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@deletionChoices_card) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.deletionChoices_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.Cardinality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => Nat.card (DeletionChoices c)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Cardinality

namespace KeptEdges

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Configuration DeletionChoices
    (fun _ => Set (Sym2 Vertex))

def actual : Realization signature :=
  realize signature (fun _ _ e => e.deletedEdges) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : Configuration) (e : DeletionChoices c) (x y : Vertex),
    ((treeFiberEquiv c).symm e).val.Adj x y ↔
      G500.Adj x y ∧ x ∈ c.vertices ∧ y ∈ c.vertices ∧ s(x, y) ∉ R.readout () c e

private def firstEdge : (cycleGraph 3).edgeSet :=
  ⟨s(0, 1), cycleGraph_adj.mpr (by decide)⟩

private def secondEdge : (cycleGraph 3).edgeSet :=
  ⟨s(0, 2), cycleGraph_adj.mpr (by decide)⟩

private def dropTriangleEdge (edge : (cycleGraph 3).edgeSet) : DeletionChoices fullTriangle :=
  ⟨(properCycleChoiceEquiv _ fullTriangleCoreMissing).symm (),
    ⟨some edge, by simp [fullTrianglePresent]⟩⟩

private theorem firstEdgeDeleted :
    s(triangle 0, triangle 1) ∈ (dropTriangleEdge firstEdge).deletedEdges :=
  Or.inr rfl

private theorem firstEdgeKept :
    s(triangle 0, triangle 1) ∉ (dropTriangleEdge secondEdge).deletedEdges := by
  intro h
  change False ∨ s(triangle 0, triangle 1) = s(triangle 0, triangle 2) at h
  rcases h with h | h
  · exact h
  · rcases Sym2.eq_iff.mp h with h | h
    · exact (by decide : triangle 1 ≠ triangle 2) h.2
    · exact (by decide : triangle 0 ≠ triangle 2) h.1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hhost : G500.Adj (triangle 0) (triangle 1) := by
    unfold G500
    exact (joinAt_inr _ _ _ _ _ _).mpr (cycleGraph_adj.mpr (by decide))
  have hleft : triangle 0 ∈ fullTriangle.vertices := by
    change (0 : Fin 3) ∈ (Finset.univ : Finset (Fin 3))
    exact Finset.mem_univ _
  have hright : triangle 1 ∈ fullTriangle.vertices := by
    change (1 : Fin 3) ∈ (Finset.univ : Finset (Fin 3))
    exact Finset.mem_univ _
  have htree := (h fullTriangle (dropTriangleEdge firstEdge) (triangle 0) (triangle 1)).mpr
    ⟨hhost, hleft, hright, by change ¬ False; exact not_false⟩
  exact ((treeFiberEquiv_keeps_edge_iff _ _ _ _).mp htree).2.2.2 firstEdgeDeleted

def family : Registration arena (type_of% @treeFiberEquiv_keeps_edge_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨treeFiberEquiv_keeps_edge_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨fullTriangle, dropTriangleEdge firstEdge, dropTriangleEdge secondEdge, ?_⟩
    intro h
    have he : (dropTriangleEdge firstEdge).deletedEdges = (dropTriangleEdge secondEdge).deletedEdges := h
    exact firstEdgeKept (he ▸ firstEdgeDeleted)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@treeFiberEquiv_keeps_edge_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.treeFiberEquiv_keeps_edge_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices.KeptEdges.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => e.deletedEdges) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end KeptEdges
end
end Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19TreeChoices
