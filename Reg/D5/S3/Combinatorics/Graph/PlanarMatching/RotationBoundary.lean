import D5.S3.Combinatorics.Graph.PlanarMatching.RotationBoundary
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source reconstruction for the actual facial-boundary readout.
Whole-family variation, sensitivity and observational dependence are separate
obligations from these reconstruction bridges. -/

namespace Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationBoundary

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

theorem face_actual : faceArena.{u}.Law actual.{u} :=
  face_bridge.mp (@Rotation.face_cycle_exact.{u})

#print axioms face_bridge
#print axioms face_actual

end
end Reg.D5.S3.Combinatorics.Graph.PlanarMatching.RotationBoundary
