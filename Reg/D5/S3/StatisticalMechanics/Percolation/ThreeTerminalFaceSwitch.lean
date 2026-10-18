import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v
noncomputable section

structure Parameters where
  Vertices : Type u
  Edges : Type v
  finiteEdges : Fintype Edges
  decidableEdges : DecidableEq Edges
  ends : Edges → Vertices × Vertices
  reference : (Edges → Bool) × (Edges → Bool)
  a : Vertices
  b : Vertices
  c : Vertices

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State _ := Mode × Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} := realize _
  (fun _ p s => by
    classical
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact (Finset.univ.filter fun q : (p.Edges → Bool) × (p.Edges → Bool) =>
      Face p.reference q ∧ graphMode (openGraph p.ends q.1) p.a p.b p.c = s.1 ∧
      graphMode (openGraph p.ends q.2) p.a p.b p.c = s.2).card)
  (fun e => nomatch e)

def bad : Realization signature.{u,v} := realize _
  (fun _ _ s => if s.1 = .ab then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law Q := ∀ {V : Type u} {E : Type v} [hE : Fintype E] [dE : DecidableEq E]
    (ends : E → V × V) (r : (E → Bool) × (E → Bool)) (a b c : V)
    (_hno : ∀ q, Face r q → graphMode (openGraph ends q.1) a b c ≠ .ac),
    let p : Parameters.{u,v} := ⟨V,E,hE,dE,ends,r,a,b,c⟩
    Q.readout () p (.separate,.all) = Q.readout () p (.ab,.bc)

private theorem rejected : ¬ arena.{u,v}.Law bad := by
  intro h
  let x : PUnit.{u+1} := PUnit.unit
  let ends : ULift.{v} Empty → PUnit.{u+1} × PUnit.{u+1} := fun e => nomatch e.down
  let f : ULift.{v} Empty → Bool := fun e => Empty.elim e.down
  let r := (f,f)
  have hno : ∀ q, Face r q → graphMode (openGraph ends q.1) x x x ≠ .ac := by
    intro q _
    simp [graphMode]
  have hh := h ends r x x x hno
  norm_num [bad,realize] at hh

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  classical
  intro i
  let x : PUnit.{u+1} := PUnit.unit
  let ends : ULift.{v} Empty → PUnit.{u+1} × PUnit.{u+1} := fun e => nomatch e.down
  let f : ULift.{v} Empty → Bool := fun e => Empty.elim e.down
  let r := (f,f)
  let p : Parameters.{u,v} := ⟨PUnit,ULift Empty,inferInstance,inferInstance,ends,r,x,x,x⟩
  refine ⟨p,(.separate,.all),(.all,.all),?_⟩
  simp [actual,realize,p,graphMode,Face]

def registration : Registration arena.{u,v} (type_of% @face_cancel.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨face_cancel,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_face_cancel : Contract.Registration (@face_cancel.{u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch.register_face_cancel
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => by
    classical
    letI := p.finiteEdges
    letI := p.decidableEdges
    exact (Finset.univ.filter fun q : (p.Edges → Bool) × (p.Edges → Bool) =>
      Face p.reference q ∧ graphMode (openGraph p.ends q.1) p.a p.b p.c = s.1 ∧
      graphMode (openGraph p.ends q.2) p.a p.b p.c = s.2).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch.register_face_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_face_cancel

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch
