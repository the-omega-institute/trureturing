import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteMatchingCoreClosure

/- UNCOMPILED semantic/source-registration attempt. The actual native
CompiledSourceScope, CompiledSourceOperands and CompiledSourceContract APIs
remain authoritative. sourceSelection is NONE because no compiled raw type,
binder coordinates or readout path has been observed. No validator execution,
enrollment or successful audit is claimed by this source. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteAcyclicFaceMatching
open _root_.D5.S3.Geometry.FiniteMatchingCoreClosure
open _root_.D5.S3.Geometry.FiniteComponentClosure (vertexComplex)

namespace Reg.D5.S3.Geometry.FiniteMatchingCoreClosure
universe u

structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  K : PreAbstractSimplicialComplex V
  matching : (letI := dv; Pairing K)
  data : (letI := fv; letI := dv; CriticalData matching)

attribute [instance] Parameters.fv Parameters.dv

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
  realize signature (fun _ p s => s ∈ p.data.C) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    {K : PreAbstractSimplicialComplex V} {M : Pairing K}
    (A : CriticalData M) (s : Finset V),
    s ∈ A.X ↔ R.readout () ⟨V, fv, dv, K, M, A⟩ s ∨ s ∈ A.critical

private theorem bridge :
    (type_of% (@CriticalData.X_core_equation.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv K M A s; exact @h V fv dv K M A s
  · intro h V fv dv K M A s; exact @h V fv dv K M A s

private def emptyMatching {V : Type u} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) : Pairing K where
  pairs := ∅
  lower_nonempty := by simp
  apex_notMem := by simp
  upper_mem := by simp
  disjoint := by simp

private def testData : CriticalData
    (emptyMatching (vertexComplex (⟨()⟩ : ULift.{u} Unit))) where
  p := ⟨()⟩
  critical := ∅
  D := 1
  positive := Nat.zero_lt_one
  point_mem := by exact Set.mem_singleton _
  critical_mem := by simp
  point_not_critical := by simp
  cardinality := by simp
  unmatched := by
    intro s hs
    constructor
    · intro _; exact Or.inl (Set.mem_singleton_iff.mp hs)
    · intro _ e he; simp [emptyMatching] at he

private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, vertexComplex ⟨()⟩,
    emptyMatching _, testData⟩

private theorem present : actual.{u}.readout () testParameters {testData.p} :=
  testData.point_in_C

private theorem absent : ¬ actual.{u}.readout () testParameters ∅ := by
  intro h
  exact Finset.not_nonempty_empty ((testData.C.isRelLowerSet_faces h).1)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.fv testParameters.dv
    testParameters.K testParameters.matching testParameters.data {testData.p}
  rcases hh.mp testData.point_in_X with hf | hc
  · exact hf
  · exact testData.point_not_critical hc

def family : Registration arena.{u} (type_of% (@CriticalData.X_core_equation.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@CriticalData.X_core_equation.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, {testData.p}, ∅, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CriticalData.X_core_equation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteMatchingCoreClosure.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteMatchingCoreClosure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => s ∈ p.data.C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteMatchingCoreClosure
