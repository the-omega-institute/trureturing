import D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The path formed by following one arm and returning along the other. -/

open SimpleGraph
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing

universe u

private abbrev WalkParameters := Σ V : Type u, Σ H W : SimpleGraph V,
  Σ a b : V, (H ⊔ W).Walk a b

private abbrev WalkSignature : Signature where
  Params := WalkParameters.{u}
  State x := (x.2.1 ⊔ x.2.2.1).Walk x.2.2.2.1 x.2.2.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ x := (x.2.1 ⊔ x.2.2.1).Walk x.2.2.2.1 x.2.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def joined : Realization WalkSignature.{u} :=
  realize WalkSignature
    (fun _ x q => x.2.2.2.2.2.append q.reverse) (fun e => nomatch e)

private def constantWalk : Realization WalkSignature.{u} :=
  realize WalkSignature (fun _ _ _ => .nil) (fun e => nomatch e)

private abbrev WalkArena : Arena where
  signature := WalkSignature.{u}
  Law R := ∀ {V : Type u} {H W : SimpleGraph V} (_hForest : H.IsAcyclic)
    {a b : V} (p q : (H ⊔ W).Walk a b)
    (_hp : p.IsPath) (_hq : q.IsPath)
    (_hJoin : ∀ e ∈ p.edges.getLast?, ∀ f ∈ q.edges.getLast?, e ≠ f)
    (_hLen : 0 < p.length + q.length),
    let closed := R.readout () ⟨V, H, W, a, b, p⟩ q
    ∃ j < closed.length,
      W.Adj (closed.getVert j) (closed.getVert (j + 1)) ∧
      ¬ H.Adj (closed.getVert j) (closed.getVert (j + 1)) ∧
      ∃ tail : H.Walk (closed.getVert (j + 1)) a, tail.IsPath ∧
        tail.support = (closed.drop (j + 1)).support ∧
        tail.length = closed.length - (j + 1) ∧
        tail.length = H.dist (closed.getVert (j + 1)) a

private abbrev Vertex := ULift.{u} (Fin 3)

private def fixed : SimpleGraph Vertex.{u} := ⊥
private def weld : SimpleGraph Vertex.{u} := ⊤

private def start : Vertex.{u} := ⟨0⟩
private def mid : Vertex.{u} := ⟨1⟩
private def goal : Vertex.{u} := ⟨2⟩

private theorem edge {x y : Vertex.{u}} (h : x.down ≠ y.down) : (fixed ⊔ weld).Adj x y := by
  simpa [fixed, weld, Ne] using h

private def direct : (fixed ⊔ weld).Walk start.{u} goal :=
  .cons (edge (by decide)) .nil

private def viaMid : (fixed ⊔ weld).Walk start.{u} goal :=
  .cons (edge (y := mid.{u}) (by decide)) (.cons (edge (by decide)) .nil)

private theorem constantWalk_invalid : ¬ WalkArena.{u}.Law constantWalk := by
  intro h
  have hImpossible := h (H := fixed.{u}) (W := weld.{u})
    (by exact SimpleGraph.isAcyclic_bot) direct viaMid
    (by
      rw [Walk.isPath_def]
      change [start.{u}, goal].Nodup
      decide)
    (by
      rw [Walk.isPath_def]
      change [start.{u}, mid, goal].Nodup
      decide)
    (by
      intro e he f hf
      change some s(start.{u}, goal) = some e at he
      change some s(mid.{u}, goal) = some f at hf
      rw [← Option.some.inj he, ← Option.some.inj hf]
      decide)
    (by decide)
  obtain ⟨j, hj, _⟩ := hImpossible
  change j < 0 at hj
  exact Nat.not_lt_zero _ hj

private theorem joined_varies :
    joined.{u}.readout () ⟨Vertex.{u}, fixed, weld, start, goal, direct⟩ direct ≠
      joined.{u}.readout () ⟨Vertex.{u}, fixed, weld, start, goal, direct⟩ viaMid := by
  intro he
  have hLengths := congrArg Walk.length he
  simp [joined, realize, direct, viaMid] at hLengths

def evidence : Registration WalkArena.{u} (type_of% (@meeting_arms_last_weld.{u})) where
  actual := joined
  bridge := Iff.rfl
  variation := ⟨@meeting_arms_last_weld.{u}, constantWalk, constantWalk_invalid⟩
  sensitivity := ⟨fun i => ⟨constantWalk,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, constantWalk_invalid⟩,
    fun e => nomatch e⟩
  dependence := fun _ =>
    ⟨⟨Vertex.{u}, fixed, weld, start, goal, direct⟩, direct, viaMid, joined_varies⟩

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@meeting_arms_last_weld.{u}) (Realization WalkSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing.meeting_arms_last_weld
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨WalkArena.{u}⟩
  objectArena := .source ⟨WalkArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WalkArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize WalkSignature
    (fun _ x q => x.2.2.2.2.2.append q.reverse) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing
