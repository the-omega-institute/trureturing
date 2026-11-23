import D5.S3.Combinatorics.Graph.DeltaY.MoveModel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for edge counts and the forward update. -/

namespace Reg.D5.S3.Combinatorics.Graph.DeltaY.MoveModel

open _root_.DeltaY
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

private abbrev signature : Signature where
  Params := Unit
  State _ := FiniteGraph.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ _ H => H.edgeCount) (fun e => nomatch e)

private def one : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G H : FiniteGraph.{u}}, SourceReach true G H → R.readout () () H = G.edgeCount

private def emptyGraph : FiniteGraph.{u} := ⟨ULift.{u} (Fin 2), ⊥, inferInstance⟩

private def fullGraph : FiniteGraph.{u} := ⟨ULift.{u} (Fin 2), ⊤, inferInstance⟩

private theorem empty_count : emptyGraph.{u}.edgeCount = 0 := by
  classical
  change Nat.card ↥((⊥ : SimpleGraph (ULift.{u} (Fin 2))).edgeSet) = 0
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet, SimpleGraph.edgeFinset_bot,
    Finset.card_empty]

private theorem full_count : fullGraph.{u}.edgeCount = 1 := by
  classical
  change Nat.card ↥((⊤ : SimpleGraph (ULift.{u} (Fin 2))).edgeSet) = 1
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

private theorem rejects_one : ¬ arena.{u}.Law one := by
  intro h
  have e := h (G := emptyGraph.{u}) Relation.ReflTransGen.refl
  change 1 = emptyGraph.{u}.edgeCount at e
  rw [empty_count] at e
  omega

private theorem edgeCount_varies : ObservationalDependence signature.{u} actual := by
  intro i
  exact ⟨(), emptyGraph, fullGraph, by
    change emptyGraph.edgeCount ≠ fullGraph.edgeCount
    rw [empty_count, full_count]
    decide⟩

noncomputable def sourceEvidence : Registration arena.{u} (type_of% (@source_strong_edge_count.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_strong_edge_count.{u}, one, rejects_one⟩
  sensitivity := ⟨fun _ => ⟨one, fun _ hj => (hj (Subsingleton.elim _ _)).elim,
    funext (fun e => nomatch e), rejects_one⟩, fun e => nomatch e⟩
  dependence := edgeCount_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@source_strong_edge_count.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `DeltaY.source_strong_edge_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DeltaY.MoveModel.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ H => H.edgeCount) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DeltaY.MoveModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Isomorphism

private abbrev isoArena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : FiniteGraph.{u}} {H : FiniteGraph.{v}},
    G.graph ≃g H.graph → R.readout () () G = H.edgeCount

private theorem rejects_one_iso : ¬ isoArena.{u,v}.Law one := by
  intro h
  let e : emptyGraph.{u}.graph ≃g emptyGraph.{v}.graph :=
    ⟨Equiv.ulift.trans Equiv.ulift.symm, Iff.rfl⟩
  have he := h e
  change 1 = emptyGraph.{v}.edgeCount at he
  rw [empty_count] at he
  omega

noncomputable def sourceEvidence : Registration isoArena.{u,v}
    (type_of% (@finiteGraph_iso_edges.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteGraph_iso_edges.{u,v}, one, rejects_one_iso⟩
  sensitivity := ⟨fun _ => ⟨one, fun _ hj => (hj (Subsingleton.elim _ _)).elim,
    funext (fun e => nomatch e), rejects_one_iso⟩, fun e => nomatch e⟩
  dependence := edgeCount_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finiteGraph_iso_edges.{u,v}) (Realization signature.{u}) Unit Unit := {
  unitName := `DeltaY.finiteGraph_iso_edges.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DeltaY.MoveModel.Isomorphism.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨isoArena⟩
  objectArena := .source ⟨isoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source isoArena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ G => G.edgeCount) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DeltaY.MoveModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Isomorphism

namespace ForwardValidity

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Triple, ℕ)
    (fun _ => State) (fun _ => State)

private def actual : Realization signature :=
  realize signature (fun _ p G => G.forward p.1 p.2) (fun e => nomatch e)

private def invalid : State := ⟨{0}, {s(0, 0)}⟩

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => invalid) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : State} {T : Triple} {o : ℕ},
    G.Valid → (R.readout () ⟨T, o⟩ G).Valid ↔ T.verts ⊆ G.active ∧ o ∉ T.verts

private def triangle : Triple := ⟨0, 1, 2, by decide, by decide, by decide⟩

private def seed : State := ⟨{0, 1, 2}, ∅⟩

private theorem rejects_invalid : ¬ arena.Law rejected := by
  intro h
  have hSeed : seed.Valid := by
    intro x y hxy
    simp [State.Adj, seed] at hxy
  have hInvalid : invalid.Valid :=
    (h (G := seed) (T := triangle) (o := 3) hSeed).mpr ⟨by decide, by decide⟩
  exact (hInvalid (x := 0) (y := 0) (by decide : invalid.Adj 0 0)).2.2 rfl

private theorem update_varies : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨triangle, 3⟩, seed, ⟨{0, 1, 2, 4}, ∅⟩, ?_⟩
  have hActive : insert 3 seed.active ≠ insert 3 ({0, 1, 2, 4} : Finset ℕ) := by decide
  exact fun h => hActive (congrArg State.active h)

def sourceEvidence : Registration arena (type_of% @forward_valid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@forward_valid, rejected, rejects_invalid⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejects_invalid
  dependence := update_varies

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@forward_valid) (Realization signature) Unit Unit := {
  unitName := `DeltaY.forward_valid.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DeltaY.MoveModel.ForwardValidity.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p G => G.forward p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DeltaY.MoveModel
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ForwardValidity

end Reg.D5.S3.Combinatorics.Graph.DeltaY.MoveModel
