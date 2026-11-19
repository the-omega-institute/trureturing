import D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The revealed graph is a varying observation of the queried local orders. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
open _root_.D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal BigOperators

namespace Reg.D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
noncomputable section
universe u
private abbrev Square := ULift.{u} (Bool × Bool)

private def flipAxis (axis : Bool) (x : Square.{u}) : Square.{u} :=
  if axis then ⟨x.down.1, !x.down.2⟩ else ⟨!x.down.1, x.down.2⟩

private theorem flipAxis_involutive (axis : Bool) : Function.Involutive (flipAxis.{u} axis) := by
  rintro ⟨a,b⟩
  cases axis <;> cases a <;> cases b <;> rfl

private theorem flipAxis_ne (axis : Bool) (x : Square.{u}) : x ≠ flipAxis axis x := by
  rcases x with ⟨a,b⟩
  cases axis <;> cases a <;> cases b <;> decide

private def axisGraph (axis : Bool) : SimpleGraph Square.{u} :=
  SimpleGraph.fromRel (fun x y => y = flipAxis axis x)

private theorem axisGraph_neighbors (axis : Bool) (x : Square.{u}) :
    (axisGraph axis).neighborSet x = {flipAxis axis x} := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, axisGraph, SimpleGraph.fromRel_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hy | hx⟩
    · exact hy
    · rw [hx, flipAxis_involutive axis y]
  · rintro rfl
    exact ⟨flipAxis_ne axis x, Or.inl rfl⟩

private def corner : Square.{u} := ⟨false, false⟩

private def queryCorner : OrderedProtocol (fun _ : Square.{u} => 1) :=
  .query corner (fun _ => .stop)

private def orders (axis : Bool) :
    NeighborOrderTable (axisGraph.{u} axis) (fun _ => 1) :=
  fun v => {
    toFun := fun _ => ⟨flipAxis axis v, by simp [axisGraph_neighbors]⟩
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun w => by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp ((axisGraph_neighbors axis v) ▸ w.2)).symm }

private theorem orderedRunsDiffer :
    runWithOrders (axisGraph.{u} false) (fun _ => 1) queryCorner (orders false) ≠
      runWithOrders (axisGraph.{u} true) (fun _ => 1) queryCorner (orders true) := by
  intro he
  change ([⟨corner, fun _ => flipAxis false corner⟩] :
    List (Sigma (OrderedResponse (fun _ : Square.{u} => 1)))) =
    [⟨corner, fun _ => flipAxis true corner⟩] at he
  have h := (List.cons.inj he).1
  have hfirst := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hcoord := congrArg (fun a : Square.{u} => a.down.1) (congrFun hfirst 0)
  exact Bool.noConfusion hcoord

private abbrev signature : Signature where
  Params := Type u
  State V := History V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := SimpleGraph V
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ hist => revealedEdges hist) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

attribute [local instance] Classical.propDecidable

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) (d : V → ℕ)
    (p : OrderedProtocol d) (g : NeighborOrderTable H d) (μ : PMF (NeighborOrderTable G d))
    (_hμ : ∀ f, μ f = (Nat.card (NeighborOrderTable G d) : ℝ≥0∞)⁻¹),
    let trace := runWithOrders H d p g
    let seen := (trace.map Sigma.fst).toFinset
    let report := R.readout () V (reportedNeighborSets trace)
    μ.toOuterMeasure {t | runWithOrders G d p t = trace} =
      if report ≤ G then ((∏ v ∈ seen, (d v).factorial : ℕ) : ℝ≥0∞)⁻¹ else 0

private theorem rejectsEmpty : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let T := NeighborOrderTable (axisGraph.{u} false) (fun _ => 1)
  let : Fintype T := Fintype.ofFinite _
  let : Nonempty T := ⟨orders false⟩
  let μ := uniformPmf T
  have hweight (f : T) : μ f = (Nat.card T : ℝ≥0∞)⁻¹ := by
    simp only [μ, uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]
  have hm := h (axisGraph false) (axisGraph true) (fun _ => 1) queryCorner (orders true) μ hweight
  let E : Set T := {t | runWithOrders (axisGraph false) (fun _ => 1) queryCorner t =
    runWithOrders (axisGraph true) (fun _ => 1) queryCorner (orders true)}
  have hEmpty : E = ∅ := by
    ext t
    change (runWithOrders (axisGraph false) (fun _ => 1) queryCorner t =
      runWithOrders (axisGraph true) (fun _ => 1) queryCorner (orders true)) ↔ False
    have heq : t = orders false := by
      funext v
      apply Equiv.ext
      intro i
      apply Subtype.ext
      have hs : (t v i).1 ∈ (axisGraph false).neighborSet v := (t v i).2
      exact Set.mem_singleton_iff.mp ((axisGraph_neighbors false v).subset hs)
    rw [heq]
    exact iff_false_intro orderedRunsDiffer
  change μ.toOuterMeasure E = _ at hm
  simp [hEmpty, rejected, realize] at hm

private theorem actualVaries :
    revealedEdges ([] : History Square.{u}) ≠
      revealedEdges [⟨corner, (axisGraph true).neighborSet corner⟩] := by
  intro heq
  have h : (revealedEdges [⟨corner, (axisGraph true).neighborSet corner⟩]).Adj
      corner (flipAxis true corner) := by
    rw [revealedEdges, SimpleGraph.fromRel_adj]
    refine ⟨flipAxis_ne true corner, Or.inl
      ⟨⟨corner, (axisGraph true).neighborSet corner⟩, List.mem_cons_self, rfl, ?_⟩⟩
    simp [axisGraph_neighbors]
  rw [← heq, revealedEdges, SimpleGraph.fromRel_adj] at h
  simp at h

def evidence : Registration arena.{u} (type_of% (@fixed_neighbor_order_likelihood.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_neighbor_order_likelihood.{u}, rejected, rejectsEmpty⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsEmpty⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨Square.{u}, [], [⟨corner, (axisGraph true).neighborSet corner⟩], actualVaries⟩


def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_neighbor_order_likelihood.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder.fixed_neighbor_order_likelihood
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ hist => revealedEdges hist) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
