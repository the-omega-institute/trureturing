import D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The recorded edges from a first arm and a prefix of a second arm. -/

open SimpleGraph
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm

universe u

private abbrev HistoryParams := Σ V : Type u, Σ G : SimpleGraph V, Σ a b : V, G.Walk a b

private abbrev HistorySignature : Signature where
  Params := HistoryParams.{u}
  State x := List (Sym2 x.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ x := List (Sym2 x.1)
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualHistory : Realization HistorySignature.{u} :=
  realize HistorySignature (fun _ x edges => x.2.2.2.2.edges ++ edges) (fun e => nomatch e)

private def extraEdge : Realization HistorySignature.{u} :=
  realize HistorySignature
    (fun _ x edges => s(x.2.2.1, x.2.2.2.1) :: (x.2.2.2.2.edges ++ edges))
    (fun e => nomatch e)

private abbrev HistoryArena : Arena where
  signature := HistorySignature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {a b c : V} (p : G.Walk a b) (q : G.Walk a c)
    (_hp : p.IsPath) (_hq : q.IsPath)
    (_hFirst : ¬ p.Nil → p.snd ≠ q.snd)
    (_hInterior : ∀ i, 0 < i → i < q.length → q.getVert i ∉ p.support)
    (j : ℕ) (_hj : j < q.length),
    let seenEdges := R.readout () ⟨V, G, a, b, p⟩ (q.take j).edges
    s(q.getVert j, q.getVert (j + 1)) ∉ seenEdges

private abbrev Vertex := ULift.{u} (Fin 3)

private def graph : SimpleGraph Vertex.{u} := ⊤
private def start : Vertex.{u} := ⟨0⟩
private def mid : Vertex.{u} := ⟨1⟩
private def goal : Vertex.{u} := ⟨2⟩

private theorem edge {x y : Vertex.{u}} (h : x.down ≠ y.down) : graph.Adj x y := by
  simpa [graph, Ne] using h

private def direct : graph.Walk start.{u} goal :=
  .cons (edge (by decide)) .nil

private def viaMid : graph.Walk start.{u} goal :=
  .cons (edge (y := mid.{u}) (by decide)) (.cons (edge (by decide)) .nil)

private theorem extraEdge_invalid : ¬ HistoryArena.{u}.Law extraEdge := by
  intro h
  have he := h viaMid.{u} direct
    (by
      rw [Walk.isPath_def]
      change [start.{u}, mid, goal].Nodup
      decide)
    (by
      rw [Walk.isPath_def]
      change [start.{u}, goal].Nodup
      decide)
    (fun _ => by
      change mid.{u} ≠ goal
      decide)
    (by
      intro i hi hit
      change i < 1 at hit
      omega)
    0 (by decide)
  apply he
  change s(start.{u}, goal) ∈ s(start.{u}, goal) :: _
  exact List.mem_cons_self

private theorem history_varies :
    actualHistory.{u}.readout () ⟨Vertex.{u}, graph, start, goal, viaMid⟩ (direct.take 0).edges ≠
      actualHistory.{u}.readout () ⟨Vertex.{u}, graph, start, goal, viaMid⟩ (direct.take 1).edges := by
  intro h
  have hLength := congrArg List.length h
  change 2 = 3 at hLength
  omega

def evidence : Registration HistoryArena.{u} (type_of% (@fresh_edge_after_first_arm.{u})) where
  actual := actualHistory
  bridge := Iff.rfl
  variation := ⟨@fresh_edge_after_first_arm.{u}, extraEdge, extraEdge_invalid⟩
  sensitivity := ⟨fun i => ⟨extraEdge,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, extraEdge_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ =>
    ⟨⟨Vertex.{u}, graph, start, goal, viaMid⟩, (direct.take 0).edges, (direct.take 1).edges, history_varies⟩

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fresh_edge_after_first_arm.{u}) (Realization HistorySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm.fresh_edge_after_first_arm
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨HistoryArena.{u}⟩
  objectArena := .source ⟨HistoryArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source HistoryArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize HistorySignature
    (fun _ x edges => x.2.2.2.2.edges ++ edges) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm
