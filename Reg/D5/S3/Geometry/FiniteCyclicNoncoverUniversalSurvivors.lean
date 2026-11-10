import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors

/- UNCOMPILED SOURCE-SHAPED ATTEMPTS. The readouts below are actual source
operands, and the laws retain the source quantifiers and endpoint clauses.
No CompiledSourceScope/Operands/Contract or Scribe validator has run. Actual
correspondence is OPEN; sourceSelection is none. Packed Parameters are a
mathematical family presentation, not an asserted source binder/selector. -/
noncomputable section
open Set Finset
open scoped unitInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteGreedyFamilyTransport
open _root_.D5.S3.Geometry.FiniteIndependentPathGreedy
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open _root_.D5.S3.Geometry.FiniteElementaryCollapse
open _root_.D5.S3.Geometry.FiniteComponentClosure
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteCoordinateTruncation
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse (faceSet mem_faceSet)
namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors

universe u

namespace remaining_zero
structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  s : Fin (3*q) ↪ V
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

def actual : Realization signature.{u} := realize signature (fun _ p a => a ∈ remainingFaces (by have hq := p.hq; omega) p.s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (a : Finset V),
    R.readout () ⟨V, fv, dv, q, hq, s⟩ a ↔ a ∈ insert {point (by omega) s} {criticalA q hq s, criticalB q hq s}
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv q hq s a
    exact Finset.ext_iff.mp (h q hq s) a
  · intro h V fv dv q hq s
    apply Finset.ext
    intro a
    exact h q hq s a
private def testEmbedding : Fin 3 ↪ ULift.{u} (Fin 3) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 3), inferInstance, inferInstance, 1, by omega, testEmbedding⟩
private def presentState : signature.State testParameters := {point (by omega) testEmbedding}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState := by
  change {point (by omega) testEmbedding} ∈ remainingFaces (by omega) testEmbedding
  rw [_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero 1 (by omega) testEmbedding]
  exact Finset.mem_insert_self _ _
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  intro h
  change ∅ ∈ remainingFaces (by omega) testEmbedding at h
  have hf := survivors_subset (faceSet (noncover (show 0 < 3 by omega) testEmbedding))
    ((List.finRange 3).map testEmbedding) h
  exact Finset.not_nonempty_empty ((mem_faceSet _ _).mp hf).1
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (V := ULift.{u} (Fin 3)) 1 (by omega) testEmbedding
    {point (by omega) testEmbedding}).mpr (by simp)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end remaining_zero

namespace remaining_one
structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  s : Fin (3*q+1) ↪ V
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

def actual : Realization signature.{u} := realize signature (fun _ p a => a ∈ remainingFaces (by have hq := p.hq; omega) p.s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) (a : Finset V),
    R.readout () ⟨V, fv, dv, q, hq, s⟩ a ↔ a ∈ insert {point (by omega) s} {criticalOne q s}
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv q hq s a
    exact Finset.ext_iff.mp (h q hq s) a
  · intro h V fv dv q hq s
    apply Finset.ext
    intro a
    exact h q hq s a
private def testEmbedding : Fin 4 ↪ ULift.{u} (Fin 4) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 4), inferInstance, inferInstance, 1, by omega, testEmbedding⟩
private def presentState : signature.State testParameters := {point (by omega) testEmbedding}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState := by
  change {point (by omega) testEmbedding} ∈ remainingFaces (by omega) testEmbedding
  rw [_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one 1 (by omega) testEmbedding]
  exact Finset.mem_insert_self _ _
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  intro h
  change ∅ ∈ remainingFaces (by omega) testEmbedding at h
  have hf := survivors_subset (faceSet (noncover (show 0 < 4 by omega) testEmbedding))
    ((List.finRange 4).map testEmbedding) h
  exact Finset.not_nonempty_empty ((mem_faceSet _ _).mp hf).1
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (V := ULift.{u} (Fin 4)) 1 (by omega) testEmbedding
    {point (by omega) testEmbedding}).mpr (by simp)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_one.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end remaining_one

namespace remaining_two
structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  s : Fin (3*q+2) ↪ V
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

def actual : Realization signature.{u} := realize signature (fun _ p a => a ∈ remainingFaces (by have hq := p.hq; omega) p.s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) (a : Finset V),
    R.readout () ⟨V, fv, dv, q, hq, s⟩ a ↔ a ∈ insert {point (by omega) s} {criticalTwo q hq s}
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv q hq s a
    exact Finset.ext_iff.mp (h q hq s) a
  · intro h V fv dv q hq s
    apply Finset.ext
    intro a
    exact h q hq s a
private def testEmbedding : Fin 5 ↪ ULift.{u} (Fin 5) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 5), inferInstance, inferInstance, 1, by omega, testEmbedding⟩
private def presentState : signature.State testParameters := {point (by omega) testEmbedding}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState := by
  change {point (by omega) testEmbedding} ∈ remainingFaces (by omega) testEmbedding
  rw [_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two 1 (by omega) testEmbedding]
  exact Finset.mem_insert_self _ _
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  intro h
  change ∅ ∈ remainingFaces (by omega) testEmbedding at h
  have hf := survivors_subset (faceSet (noncover (show 0 < 5 by omega) testEmbedding))
    ((List.finRange 5).map testEmbedding) h
  exact Finset.not_nonempty_empty ((mem_faceSet _ _).mp hf).1
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (V := ULift.{u} (Fin 5)) 1 (by omega) testEmbedding
    {point (by omega) testEmbedding}).mpr (by simp)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors.remaining_two.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end remaining_two

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors
