import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction

/- SOURCE-ONLY REPAIR; UNCOMPILED.
The binding is the unchanged original @first_round.{u}. Only its literal RHS
singleton {point hn s} is abstracted, with its actual point hn s as state input.
The readout is singleton on V; Parameters contains only the ambient data type.
The full original equality and telescope remain in arena.Law. SourceSelection
stays none; no compiled selection, kernel acceptance or enrollment is claimed. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse (faceSet mem_faceSet)

namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
universe u

abbrev Parameters := Type u

abbrev signature : Signature where
  Params := Parameters.{u}
  State V := V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Finset V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun (_ : Unit) (V : Type u) (v : V) => ({v} : Finset V))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature
    (fun (_ : Unit) (V : Type u) (_ : V) => (∅ : Finset V))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] {n : Nat}
    (hn : 3 ≤ n) (s : Fin n ↪ V),
    remaining (faceSet (noncover (show 0 < n by omega) s)) (point hn s) =
      insert (R.readout () V (point hn s)) (tailFaces hn s)

private theorem bridge : (type_of% (@first_round.{u})) ↔ arena.{u}.Law actual :=
  Iff.rfl

private def testParameters : Parameters.{u} := ULift.{u} (Fin 3)

private def testSpokes : Fin 3 ↪ testParameters.{u} :=
  ⟨ULift.up, fun _ _ h => congrArg ULift.down h⟩

private def presentState : signature.State testParameters.{u} := ULift.up (0 : Fin 3)
private def absentState : signature.State testParameters.{u} := ULift.up (1 : Fin 3)

-- The rejected equality inserts the empty face, which no faceSet can contain.
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let hn : 3 ≤ 3 := by omega
  let K : PreAbstractSimplicialComplex testParameters.{u} :=
    noncover (show 0 < 3 by omega) testSpokes.{u}
  have hh : remaining (faceSet K) (point hn testSpokes.{u}) =
      insert (∅ : Finset testParameters.{u}) (tailFaces hn testSpokes.{u}) :=
    @h testParameters.{u} (inferInstance : Fintype testParameters.{u})
      (inferInstance : DecidableEq testParameters.{u}) 3 hn testSpokes.{u}
  have he : (∅ : Finset testParameters.{u}) ∈
      remaining (faceSet K) (point hn testSpokes.{u}) := by
    rw [hh]
    exact Finset.mem_insert_self _ _
  have hface : (∅ : Finset testParameters.{u}) ∈ faceSet K :=
    remaining_subset _ _ he
  exact Finset.not_nonempty_empty
    ((K.isRelLowerSet_faces ((mem_faceSet K ∅).mp hface)).1)

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
    refine ⟨testParameters.{u}, presentState.{u}, absentState.{u}, ?_⟩
    change ({presentState.{u}} : Finset testParameters.{u}) ≠ {absentState.{u}}
    intro he
    have hm : presentState.{u} ∈ ({absentState.{u}} : Finset testParameters.{u}) := by
      rw [← he]
      exact Finset.mem_singleton_self _
    have hxy : presentState.{u} = absentState.{u} := Finset.mem_singleton.mp hm
    have hv := congrArg (fun x : testParameters.{u} => x.down.val) hxy
    change (0 : Nat) = 1 at hv
    omega

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
  readout := some (realize signature
    (fun (_ : Unit) (V : Type u) (v : V) => ({v} : Finset V))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
