import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteVertexCylinder

noncomputable section

open Set
open scoped unitInterval ContinuousMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteVertexCylinder

namespace Reg.D5.S3.Geometry.FiniteVertexCylinder

universe u w

namespace Fixed

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  complex : PreAbstractSimplicialComplex V
  vertex : V
  vertexFace : ({vertex} : Finset V) ∈ complex

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Cylinder p.complex p.vertex p.vertexFace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Space p.complex × I
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z => (retraction p.complex p.vertex p.vertexFace z.val).val)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => (vertexPoint p.complex p.vertex p.vertexFace, 0))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (z : Cylinder p.complex p.vertex p.vertexFace),
    R.readout () p z = z.val

private theorem bridge :
    (type_of% (@retraction_fixed.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p z
    exact h p.complex p.vertex p.vertexFace z
  · intro h V fv dv M v hv z
    exact h ⟨V, fv, dv, M, v, hv⟩ z

private abbrev sample : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, ⊤, ⟨()⟩, by exact Finset.singleton_nonempty _⟩

private def bottom : signature.State sample :=
  ⟨(vertexPoint sample.complex sample.vertex sample.vertexFace, 0), Or.inl rfl⟩

private def top : signature.State sample :=
  ⟨(vertexPoint sample.complex sample.vertex sample.vertexFace, 1), Or.inr rfl⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := congrArg Prod.snd (h sample top)
  change (0 : I) = 1 at hh
  exact zero_ne_one hh

def family : Registration arena.{u} (type_of% (@retraction_fixed.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@retraction_fixed.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨sample, bottom, top, ?_⟩
    intro h
    have hb := retraction_fixed sample.complex sample.vertex sample.vertexFace bottom
    have ht := retraction_fixed sample.complex sample.vertex sample.vertexFace top
    change (retraction sample.complex sample.vertex sample.vertexFace bottom.val).val =
      (retraction sample.complex sample.vertex sample.vertexFace top.val).val at h
    rw [hb, ht] at h
    exact zero_ne_one (congrArg Prod.snd h)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@retraction_fixed.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteVertexCylinder.Fixed.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteVertexCylinder.Fixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z => (retraction p.complex p.vertex p.vertexFace z.val).val)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteVertexCylinder
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Fixed

namespace Extension

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  complex : PreAbstractSimplicialComplex V
  vertex : V
  vertexFace : ({vertex} : Finset V) ∈ complex
  Y : Type w
  topology : TopologicalSpace Y
  initial :
    letI := finiteVertices
    letI := decidableVertices
    letI := topology
    C(Space complex, Y)

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices Parameters.topology

abbrev signature : Signature where
  Params := Parameters.{u,w}
  State p := C(I, p.Y)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C(I, p.Y)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,w} :=
  realize signature (fun _ _ h => h) (fun e => nomatch e)

def rejected : Realization signature.{u,w} :=
  realize signature (fun _ _ h => ContinuousMap.const _ (h 1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,w}
  Law R := ∀ (p : Parameters.{u,w}) (h : C(I, p.Y)),
    h 0 = p.initial (vertexPoint p.complex p.vertex p.vertexFace) →
    ∃ F : C(Space p.complex × I, p.Y), (∀ x, F (x, 0) = p.initial x) ∧
      ∀ t, F (vertexPoint p.complex p.vertex p.vertexFace, t) = R.readout () p h t

private theorem bridge :
    (type_of% (@vertex_homotopy_extension.{u,w})) ↔ arena.{u,w}.Law actual := by
  constructor
  · intro h p path hzero
    exact h p.complex p.vertex p.vertexFace p.initial path hzero
  · intro h V fv dv M v hv Y ty f path hzero
    exact h ⟨V, fv, dv, M, v, hv, Y, ty, f⟩ path hzero

private abbrev sample : Parameters.{u,w} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, ⊤, ⟨()⟩, by exact Finset.singleton_nonempty _,
    ULift.{w} I, inferInstance, ContinuousMap.const _ ⟨0⟩⟩

private def path : signature.State sample :=
  ⟨fun t => ⟨t⟩, continuous_uliftUp⟩

private theorem rejected_law : ¬ arena.{u,w}.Law rejected := by
  intro h
  obtain ⟨F, hf, hp⟩ := h sample path rfl
  have hh := (hf (vertexPoint sample.complex sample.vertex sample.vertexFace)).symm.trans (hp 0)
  have h01 := congrArg ULift.down hh
  change (0 : I) = 1 at h01
  exact zero_ne_one h01

def family : Registration arena.{u,w} (type_of% (@vertex_homotopy_extension.{u,w})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@vertex_homotopy_extension.{u,w}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨sample, ContinuousMap.const _ ⟨0⟩, ContinuousMap.const _ ⟨1⟩, ?_⟩
    intro h
    have hh := congrArg (fun f : C(I, sample.Y) => (f 0).down) h
    exact zero_ne_one hh

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@vertex_homotopy_extension.{u,w}) (Realization signature.{u,w}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteVertexCylinder.Extension.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteVertexCylinder.Extension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ h => h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteVertexCylinder
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extension

#print axioms Fixed.registration
#print axioms Extension.registration

end Reg.D5.S3.Geometry.FiniteVertexCylinder
