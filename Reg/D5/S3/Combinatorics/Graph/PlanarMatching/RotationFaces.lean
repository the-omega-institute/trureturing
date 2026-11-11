import D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source reconstruction for the actual facial-boundary readout.
Whole-family variation, sensitivity and observational dependence are separate
obligations from these reconstruction bridges. -/

namespace Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces

open SimpleGraph LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.PlanarMatching
open _root_.D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

structure Params where
  V : Type u
  vertices : Fintype V
  vertexEq : DecidableEq V
  G : SimpleGraph V
  adjacency : DecidableRel G.Adj
  R : Rotation G

attribute [instance] Params.vertices Params.vertexEq Params.adjacency

def signature : Signature where
  Params := Params.{u}
  State p := p.R.Face → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.G.edgeSet → ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => p.R.boundary x) (fun e => nomatch e)

def model (p : Params.{u}) : Prop :=
  p.G.Connected ∧ Nonempty p.G.Dart ∧
    (Fintype.card p.V : ℤ) - (Nat.card p.G.edgeSet : ℤ) + (Nat.card p.R.Face : ℤ) = 2

def faceLaw (L : Realization signature.{u}) : Prop :=
  ∀ p, model p →
    (∀ (x : p.R.Face → ZMod 2) (d : p.G.Dart),
      L.readout () p x ⟨d.edge,d.edge_mem⟩ = x (p.R.face d) + x (p.R.face d.symm)) ∧
    (∀ x : p.R.Face → ZMod 2, L.readout () p x = (fun _ => (0 : ZMod 2)) ↔ ∃ c, x = fun _ => c) ∧
    Set.range (L.readout () p) = (simpleCycleSpace p.G : Set (p.G.edgeSet → ZMod 2))

def faceArena : Arena := ⟨signature, faceLaw⟩

theorem face_bridge :
    (type_of% @Rotation.face_cycle_exact.{u}) ↔ faceArena.{u}.Law actual.{u} := by
  change _ ↔ faceLaw actual
  constructor
  · intro h p ⟨hc,he,hE⟩
    have hp := @h p.V p.G p.R p.vertices p.vertexEq p.adjacency hc he hE
    exact ⟨hp.1, hp.2.1, congrArg (fun s : Submodule (ZMod 2) (p.G.edgeSet → ZMod 2) =>
      (s : Set (p.G.edgeSet → ZMod 2))) hp.2.2⟩
  · intro h V G R fV dV dG hc he hE
    let p : Params := ⟨V,fV,dV,G,dG,R⟩
    have hp := h p ⟨hc,he,hE⟩
    exact ⟨hp.1, hp.2.1, SetLike.coe_injective hp.2.2⟩

def sideLaw (L : Realization signature.{u}) : Prop :=
  ∀ p, model p → ∀ (a : p.V) (q : p.G.Walk a a), q.IsCycle →
    ∃ (x : p.R.Face → ZMod 2) (I J : Set p.V),
      (∃ f, x f = 1) ∧ (∃ f, x f = 0) ∧
      L.readout () p x = (fun e : p.G.edgeSet => if e.val ∈ q.edges then 1 else 0) ∧
      (∃ r : p.G.Walk a a, (r = q ∨ r = q.reverse) ∧ ∀ d : p.G.Dart,
        ((x (p.R.face d) = 1 ∧ x (p.R.face d.symm) = 0) ↔ d ∈ r.darts) ∧
        ((x (p.R.face d) = 0 ∧ x (p.R.face d.symm) = 1) ↔ d ∈ r.reverse.darts)) ∧
      (∀ v, v ∉ q.support ↔ v ∈ I ∨ v ∈ J) ∧ Disjoint I J ∧
      (∀ d : p.G.Dart, d.fst ∉ q.support →
        (d.fst ∈ I ↔ x (p.R.face d) = 1) ∧ (d.fst ∈ J ↔ x (p.R.face d) = 0)) ∧
      (∀ v ∈ I, ∀ w ∈ J, ¬p.G.Adj v w) ∧
      (∀ (S : Set p.V) (b : ZMod 2), (S = I ∧ b = 1) ∨ (S = J ∧ b = 0) →
        ∃ H : p.G.Subgraph,
          H.verts = {v | v ∈ q.support ∨ v ∈ S} ∧
          (∀ d : p.G.Dart, H.Adj d.fst d.snd ↔
            d.edge ∈ q.edges ∨ (x (p.R.face d) = b ∧ x (p.R.face d.symm) = b)) ∧ H.Connected ∧
          (Nat.card H.verts : ℤ) - (Nat.card H.coe.edgeSet : ℤ) +
            (Nat.card {f | x f = b} : ℤ) = 1 ∧
          (Nat.card S : ℤ) - ((H.edgeSet \ q.toSubgraph.edgeSet).ncard : ℤ) +
            (Nat.card {f | x f = b} : ℤ) = 1) ∧
      (∀ M : (p.G.induce {v | v ∉ q.support}).Subgraph, M.IsPerfectMatching →
        (∀ S ∈ ({I, J} : Set (Set p.V)),
          ∃ N : ((p.G.induce {v | v ∉ q.support}).induce {v | v.val ∈ S}).Subgraph,
            N.IsPerfectMatching ∧ ∀ v w, N.Adj v w ↔ M.Adj v.val w.val) ∧
        Even (Nat.card I) ∧ Even (Nat.card J))

def sideArena : Arena := ⟨signature, sideLaw⟩

theorem side_bridge :
    (type_of% @Rotation.cycle_face_sides.{u}) ↔ sideArena.{u}.Law actual.{u} := by
  change _ ↔ sideLaw actual
  constructor
  · intro h p ⟨hc,he,hE⟩ a q hq
    exact @h p.V p.G p.R p.vertices p.vertexEq p.adjacency hc he hE a q hq
  · intro h V G R fV dV dG hc he hE a q hq
    exact h ⟨V,fV,dV,G,dG,R⟩ ⟨hc,he,hE⟩ a q hq

#print axioms face_bridge
#print axioms side_bridge

end
end Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces
