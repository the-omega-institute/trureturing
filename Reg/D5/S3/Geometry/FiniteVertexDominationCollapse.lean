import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteVertexDominationCollapse

/- UNCOMPILED AUDIT ATTEMPT. The semantic family below observes the actual
   complete lower-face list, at the raw theorem's Finset state operand.
   Native sourceSelection is deliberately NONE: no elaborated occurrence path,
   binder coordinate vector, scope check, or source-observation audit was run.
   This file does not claim enrollment/admission. The missing native observation
   must be filled from the actual elaborated theorem by the integration owner;
   the semantic family alone does not discharge it. -/

noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteGraphVertexSubstitution
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse

namespace Reg.D5.S3.Geometry.FiniteVertexDominationCollapse
universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  K : PreAbstractSimplicialComplex V
  u : V
  v : V
  distinct : u ≠ v
  extension : (letI : DecidableEq V := decidableVertices; Extends K u v)

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p s => s ∈ orderedLowers p.K p.u p.v p.distinct p.extension)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

/-- Preserve every raw theorem parameter; the state is the ORIGINAL face s. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (K : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (hExt : Extends K u v) (s : Finset V),
    R.readout () ⟨V, fv, dv, K, u, v, huv, hExt⟩ s ↔
      s ∈ K ∧ v ∈ s ∧ u ∉ s

private theorem bridge :
    (type_of% (@orderedLowers_mem.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv K u v huv hExt s
    exact @h V fv dv K u v huv hExt s
  · intro h V fv dv K u v huv hExt s
    exact @h V fv dv K u v huv hExt s

private abbrev testParameters : Parameters.{u} where
  V := ULift.{u} Bool
  finiteVertices := inferInstance
  decidableVertices := inferInstance
  K := restricted (⊥ : SimpleGraph (ULift.{u} Bool)) (fun _ => True)
  u := ⟨false⟩
  v := ⟨true⟩
  distinct := by intro h; exact Bool.false_ne_true (congrArg ULift.down h)
  extension := graph_extends _ _ _ _
    (by intro h; exact Bool.false_ne_true (congrArg ULift.down h)) trivial
    (by intro a _ ha; simp at ha)

private theorem test_face : ({testParameters.{u}.v} : Finset testParameters.V) ∈
    testParameters.K := by
  refine ⟨Finset.singleton_nonempty _, ?_, fun _ _ => trivial⟩
  intro a ha b hb hab hadj
  exact hadj

private theorem test_present :
    actual.{u}.readout () testParameters {testParameters.v} := by
  exact (orderedLowers_mem testParameters.K testParameters.u testParameters.v
    testParameters.distinct testParameters.extension _).2
      ⟨test_face, by simp, by simpa using testParameters.distinct⟩

private theorem test_absent :
    ¬ actual.{u}.readout () testParameters ∅ := by
  intro h
  have hh := (orderedLowers_mem testParameters.K testParameters.u testParameters.v
    testParameters.distinct testParameters.extension _).1 h
  exact Finset.notMem_empty _ hh.2.1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.finiteVertices
    testParameters.decidableVertices testParameters.K testParameters.u testParameters.v
    testParameters.distinct testParameters.extension {testParameters.v}
  exact hh.mpr ⟨test_face, by simp, by simpa using testParameters.distinct⟩

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨testParameters, {testParameters.v}, ∅, ?_⟩
  intro he
  exact test_absent (he ▸ test_present)

/-- Genuine semantic witnesses; this record does not grant native enrollment. -/
def family : Registration arena.{u} (type_of% (@orderedLowers_mem.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@orderedLowers_mem.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

/-- Truthful unresolved native registration attempt. sourceSelection = none
is a MISSING OBLIGATION, never a waiver or a successful audit receipt. -/
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orderedLowers_mem.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteVertexDominationCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteVertexDominationCollapse.family
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
    (fun _ p s => s ∈ orderedLowers p.K p.u p.v p.distinct p.extension)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteVertexDominationCollapse
