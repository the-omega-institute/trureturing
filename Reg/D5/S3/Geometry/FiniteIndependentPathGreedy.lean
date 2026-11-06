import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteIndependentPathGreedy

/- UNCOMPILED source-operand registration ATTEMPT. Correspondence is OPEN.
No source scope/operand/contract validator was executed, no raw binder selector
is invented, and sourceSelection remains none. This is not a green audit. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteIndependentPathGreedy

namespace Reg.D5.S3.Geometry.FiniteIndependentPathGreedy
universe u

structure Parameters where
  V : Type u
  dv : DecidableEq V
attribute [instance] Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := List p.V × Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z => z.2 ∈ survivors (paths z.1) z.1) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [dv : DecidableEq V] (vs : List V) (hd : vs.Nodup) (a : Finset V),
    R.readout () ⟨V, dv⟩ (vs, a) ↔ a ∈ pathCritical vs

private theorem bridge : (type_of% (@survivors_paths.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V dv vs hd a
    exact Finset.ext_iff.mp (@h V dv vs hd) a
  · intro h V dv vs hd
    apply Finset.ext
    intro a
    exact @h V dv vs hd a

private def testParameters : Parameters.{u} := ⟨ULift.{u} (Fin 1), inferInstance⟩
private def presentState : signature.State testParameters := ([], ∅)
private def absentState : signature.State testParameters := ([], {ULift.up ⟨0, by omega⟩})
private theorem present : actual.{u}.readout () testParameters presentState := by
  simp [actual, realize, presentState, survivors, paths]
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  simp [actual, realize, absentState, survivors, paths]
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.dv [] (by simp) ∅
  exact hh.mpr (by simp [pathCritical])

private theorem source_law : arena.{u}.Law actual := bridge.mp (@survivors_paths.{u})

def family : Registration arena.{u} (type_of% (@survivors_paths.{u})) where
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
    (@survivors_paths.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteIndependentPathGreedy.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteIndependentPathGreedy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => z.2 ∈ survivors (paths z.1) z.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteIndependentPathGreedy
