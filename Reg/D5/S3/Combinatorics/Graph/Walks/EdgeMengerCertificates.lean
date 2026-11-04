import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates

/-! Source-bound edge-list observation for the complete finite edge-Menger iff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates

open LeanInformationAudit
open SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev Parameters := Σ V : Type u, Σ _G : SimpleGraph V, Σ k : Nat,
  Σ _u : V, Σ _v : V, Fin k

def signature : Signature where
  Params := Parameters.{u}
  State p := p.2.1.Walk p.2.2.2.1 p.2.2.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Sym2 p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : Nat) (u v : V),
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (R.readout () ⟨V, G, k, u, v, i⟩ (p i)).Disjoint (p j).edges

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => []) (fun e _ => Empty.elim e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let V : Type u := ULift.{u} Bool
  let G : SimpleGraph V := completeGraph V
  let a : V := ⟨false⟩
  let b : V := ⟨true⟩
  have hab : G.Adj a b := by
    change (⟨false⟩ : V) ≠ ⟨true⟩
    intro he
    cases congrArg ULift.down he
  let p : G.Walk a b := Walk.cons hab Walk.nil
  have hp : p.IsPath := Walk.IsPath.cons Walk.IsPath.nil (by simpa using hab.ne)
  have hbad : G.IsEdgeReachable 2 a b := (h G 2 a b).2
    ⟨fun _ => p, fun _ => hp, fun _ _ _ => by simp [rejected, realize]⟩
  have hbot : G.deleteEdges {s(a, b)} = ⊥ := by
    ext x y
    simp only [deleteEdges_adj, G, completeGraph_eq_top, top_adj, bot_adj]
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y <;> simp [a, b, Sym2.eq_swap]
  have hr := hbad (s := {s(a, b)}) (by simp)
  rw [hbot, reachable_bot] at hr
  exact hab.ne hr

def family : Registration arena.{u} (type_of% (@isEdgeReachable_iff.{u})) where
  actual := realize signature
    (fun (_ : Unit) (p : Parameters.{u}) (w : signature.State p) => w.edges)
    (fun (e : Empty) (_ : Parameters.{u}) => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@isEdgeReachable_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let V : Type u := ULift.{u} Bool
    let G : SimpleGraph V := completeGraph V
    let a : V := ⟨false⟩
    let b : V := ⟨true⟩
    have hab : G.Adj a b := by
      change (⟨false⟩ : V) ≠ ⟨true⟩
      intro he
      cases congrArg ULift.down he
    let p : G.Walk a a := Walk.nil
    let q : G.Walk a a := Walk.cons hab (Walk.cons hab.symm Walk.nil)
    refine ⟨⟨V, G, 1, a, a, 0⟩, p, q, ?_⟩
    change p.edges ≠ q.edges
    intro he
    have hl := congrArg List.length he
    norm_num [p, q] at hl

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@isEdgeReachable_iff.{u}) (Realization signature.{u}) Type Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates.isEdgeReachable_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (p : Parameters.{u}) (w : signature.State p) => w.edges)
    (fun (e : Empty) (_ : Parameters.{u}) => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates
    definition := none
    coordinates := #[0, 2, 3, 4, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates
