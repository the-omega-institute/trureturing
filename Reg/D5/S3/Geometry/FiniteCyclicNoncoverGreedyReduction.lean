import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction

/- UNCOMPILED source-operand registration ATTEMPT. Correspondence is OPEN.
No source scope/operand/contract validator was executed, no raw binder selector
is invented, and sourceSelection remains none. This is not a green audit. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse (faceSet)

namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
universe u

structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  n : Nat
  hn : 3 ≤ n
  spokes : Fin n ↪ V
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
  realize signature
    (fun _ p a => a ∈ remaining (faceSet (noncover (show 0 < p.n by omega) p.spokes))
      (point p.hn p.spokes)) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] {n : Nat}
    (hn : 3 ≤ n) (s : Fin n ↪ V) (a : Finset V),
    R.readout () ⟨V, fv, dv, n, hn, s⟩ a ↔ a ∈ insert {point hn s} (tailFaces hn s)

private theorem bridge : (type_of% (@first_round.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv n hn s a
    exact Finset.ext_iff.mp (@h V fv dv n hn s) a
  · intro h V fv dv n hn s
    apply Finset.ext
    intro a
    exact @h V fv dv n hn s a

private def testParameters : Parameters.{u} where
  V := ULift.{u} (Fin 3)
  fv := inferInstance
  dv := inferInstance
  n := 3
  hn := by omega
  spokes := ⟨ULift.up, fun _ _ h => congrArg ULift.down h⟩
private def presentState : signature.State testParameters :=
  {point testParameters.hn testParameters.spokes}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState := by
  change presentState ∈ remaining (faceSet (noncover (by omega) testParameters.spokes))
    (point testParameters.hn testParameters.spokes)
  rw [first_round]
  exact Finset.mem_insert_self _ _
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  change (∅ : Finset testParameters.V) ∉ remaining
    (faceSet (noncover (by omega) testParameters.spokes)) (point testParameters.hn testParameters.spokes)
  rw [first_round]
  simp [tailFaces]
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.fv testParameters.dv 3
    testParameters.hn testParameters.spokes presentState
  exact hh.mpr (Finset.mem_insert_self _ _)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@first_round.{u})

def family : Registration arena.{u} (type_of% (@first_round.{u})) where
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
    (@first_round.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => a ∈ remaining (faceSet (noncover (show 0 < p.n by omega) p.spokes)) (point p.hn p.spokes)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
