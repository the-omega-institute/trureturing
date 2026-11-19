import D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The recorded edge graph is a varying observation of a complete transcript. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory

namespace Reg.D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory

noncomputable section

section Counterexample
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

private def queryCorner : PassiveProtocol Square.{u} (fun _ => Set Square.{u}) :=
  .query corner (fun _ => .stop)

private theorem matchings_different_history :
    runPassiveProtocol readNeighbors queryCorner.{u} (axisGraph false) ≠
      runPassiveProtocol readNeighbors queryCorner.{u} (axisGraph true) := by
  intro he
  simp only [queryCorner, runPassiveProtocol, readNeighbors, axisGraph_neighbors,
    List.cons.injEq] at he
  have h := congrArg (fun z : Σ _ : Square.{u}, Set Square.{u} => z.2) he.1
  have hn := (Set.singleton_eq_singleton_iff.mp h)
  exact Bool.noConfusion (congrArg (fun z : Square.{u} => z.down.1) hn)

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev historySignature : Signature where
  Params := Type u
  State V := History V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := SimpleGraph V
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualEdges : Realization historySignature.{u} :=
  realize historySignature (fun _ _ hist => revealedEdges hist) (fun e => nomatch e)

private def noEdges : Realization historySignature.{u} :=
  realize historySignature (fun _ _ _ => ⊥) (fun e => nomatch e)

private abbrev historyArena : Arena where
  signature := historySignature.{u}
  Law r := ∀ {W : Type u} [Finite W] (G H : SimpleGraph W)
    (p : PassiveProtocol W (fun _ => Set W)),
    runPassiveProtocol readNeighbors p G = runPassiveProtocol readNeighbors p H ↔
      r.readout () W (runPassiveProtocol readNeighbors p H) ≤ G ∧
      ∀ entry ∈ runPassiveProtocol readNeighbors p H,
        (G.neighborSet entry.1).ncard ≤ entry.2.ncard

private theorem rejectsNoEdges : ¬ historyArena.{u}.Law noEdges := by
  intro h
  apply matchings_different_history
  apply (h (axisGraph false) (axisGraph true) queryCorner).mpr
  refine ⟨bot_le, ?_⟩
  intro entry he
  simp only [queryCorner, runPassiveProtocol, readNeighbors, List.mem_cons, List.not_mem_nil,
    or_false] at he
  subst entry
  simp [axisGraph_neighbors]

private theorem actualEdges_vary :
    revealedEdges ([] : History Square.{u}) ≠
      revealedEdges (runPassiveProtocol readNeighbors queryCorner (axisGraph true)) := by
  intro heq
  have edge : (revealedEdges
      (runPassiveProtocol readNeighbors queryCorner (axisGraph true))).Adj
      corner (flipAxis true corner) := by
    rw [revealedEdges, SimpleGraph.fromRel_adj]
    refine ⟨flipAxis_ne true corner, Or.inl ⟨⟨corner, (axisGraph true).neighborSet corner⟩, ?_, rfl, ?_⟩⟩
    · rw [queryCorner, runPassiveProtocol]
      exact List.mem_cons_self
    · rw [axisGraph_neighbors]
      exact Set.mem_singleton _
  rw [← heq, revealedEdges, SimpleGraph.fromRel_adj] at edge
  simp at edge

def evidence : Registration historyArena.{u} (type_of% (@history_eq_iff_extension.{u})) where
  actual := actualEdges
  bridge := Iff.rfl
  variation := ⟨@history_eq_iff_extension.{u}, noEdges, rejectsNoEdges⟩
  sensitivity := ⟨fun i => ⟨noEdges,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsNoEdges⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨Square.{u}, [],
    runPassiveProtocol readNeighbors queryCorner (axisGraph true), actualEdges_vary⟩


def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@history_eq_iff_extension.{u}) (Realization historySignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory.history_eq_iff_extension
  realizationName := `Reg.D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨historyArena.{u}⟩
  objectArena := .source ⟨historyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source historyArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize historySignature (fun _ _ hist => revealedEdges hist) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Counterexample

end
end Reg.D5.S3.Combinatorics.Graph.CompleteNeighborhoodHistory
