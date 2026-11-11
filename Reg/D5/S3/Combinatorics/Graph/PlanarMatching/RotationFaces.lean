import D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces
import Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationBoundary

namespace Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces

open SimpleGraph LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.PlanarMatching
open _root_.D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationBoundary

universe u
noncomputable section

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

def orientationSignature : Signature where
  Params := Params.{u}
  State p := p.G.Dart → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.R.Face → ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def orientationActual : Realization orientationSignature :=
  realize orientationSignature (fun _ p ε =>
    @Rotation.faceOpposition p.V p.G p.R p.vertices p.adjacency ε) (fun e => nomatch e)

def orientationLaw (L : Realization orientationSignature.{u}) : Prop :=
  ∀ p, model p → Even (Fintype.card p.V) →
    ∃ ε : p.G.Dart → ZMod 2,
      (∀ d, ε d.symm = 1 + ε d) ∧ (∀ f, L.readout () p ε f = 1) ∧
      ∀ (a : p.V) (q : p.G.Walk a a), q.IsCycle → Even q.length →
        ∀ M : (p.G.induce {v | v ∉ q.support}).Subgraph, M.IsPerfectMatching →
          (q.darts.map ε).sum = 1

def orientationArena : Arena := ⟨orientationSignature,orientationLaw⟩

theorem orientation_bridge :
    (type_of% @Rotation.face_odd_nice_cycle_orientation.{u}) ↔
      orientationArena.{u}.Law orientationActual.{u} := by
  change _ ↔ orientationLaw orientationActual
  constructor
  · intro h p ⟨hc,he,hE⟩ hEven
    exact @h p.V p.G p.R p.vertices p.vertexEq p.adjacency hc he hE hEven
  · intro h V G R fV dV dG hc he hE hEven
    exact h ⟨V,fV,dV,G,dG,R⟩ ⟨hc,he,hE⟩ hEven

theorem side_actual : sideArena.{u}.Law actual.{u} :=
  side_bridge.mp (@Rotation.cycle_face_sides.{u})

theorem orientation_actual : orientationArena.{u}.Law orientationActual.{u} :=
  orientation_bridge.mp (@Rotation.face_odd_nice_cycle_orientation.{u})

#print axioms orientation_bridge

#print axioms side_bridge

end
end Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces
