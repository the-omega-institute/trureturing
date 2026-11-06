/- UNCOMPILED REG/source-observation ATTEMPT.

   This mirror observes the exact raw incidence readout `s ∈ rootK`.  It does
   not claim a native source selector, enrollment, declared_validated status,
   admission, or a judgment about the recursive collapse. The latest vertex
   Parameters stored-instance repair is a separately bound prerequisite.
-/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteIncidenceRootCollapse

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteIncidenceRootCollapse

namespace Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse
universe u

structure Parameters where
  I : Type u
  J : Type u
  finiteI : Fintype I
  decidableI : DecidableEq I
  finiteJ : Fintype J
  decidableJ : DecidableEq J
  relation : I → J → Prop
  state : State relation

attribute [instance] Parameters.finiteI Parameters.decidableI
attribute [instance] Parameters.finiteJ Parameters.decidableJ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p s => s ∈ rootK p.relation p.state)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (s : Finset p.I),
    R.readout () p s ↔ s ∈ rootK p.relation p.state

private theorem bridge :
    (type_of% (@mem_rootK.{u,u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p s
    exact (h p.relation p.state s)
  · intro h
    -- mem_rootK is a definitional membership presentation. Avoid guessing
    -- which unused section dictionaries occur in its elaborated telescope.
    intros
    exact Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p : Parameters.{u} := {
    I := ULift.{u} Bool
    J := ULift.{u} Unit
    finiteI := inferInstance
    decidableI := inferInstance
    finiteJ := inferInstance
    decidableJ := inferInstance
    relation := fun _ _ => False
    state := { active := {⟨false⟩}, rows := {⟨()⟩} } }
  have hs : ({⟨false⟩} : Finset p.I) ∈ rootK p.relation p.state := by
    refine ⟨by simp, ⟨⟨()⟩, by simp, ?_⟩⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hx, by simp [p]⟩
  exact (h p {⟨false⟩}).mpr hs

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : Parameters.{u} := {
    I := ULift.{u} Bool
    J := ULift.{u} Unit
    finiteI := inferInstance
    decidableI := inferInstance
    finiteJ := inferInstance
    decidableJ := inferInstance
    relation := fun _ _ => False
    state := { active := {⟨false⟩}, rows := {⟨()⟩} } }
  refine ⟨p, {⟨false⟩}, ∅, ?_⟩
  intro h
  have hp : ({⟨false⟩} : Finset p.I) ∈ rootK p.relation p.state := by
    refine ⟨by simp, ⟨⟨()⟩, by simp, ?_⟩⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hx, by simp [p]⟩
  have he : actual.readout i p (∅ : Finset p.I) := h ▸ hp
  change (∅ : Finset p.I) ∈ rootK p.relation p.state at he
  exact he.1.ne_empty rfl

def family : Registration arena.{u} (type_of% (@mem_rootK.{u,u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@mem_rootK.{u,u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_rootK.{u,u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse.family
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
    (fun _ p s => s ∈ rootK p.relation p.state)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/- No `declared_validated` claim. This equal-universe mem_rootK family is
   not an audit of build, Result, critical data, maps or independent universes.
   Native telescope/dictionary correspondence, source selection, enrollment,
   bundle/variation/sensitivity audits and owner coverage remain open. -/

end Reg.D5.S3.Geometry.FiniteIncidenceRootCollapse
