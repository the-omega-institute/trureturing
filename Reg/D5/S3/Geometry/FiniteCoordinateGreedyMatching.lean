import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCoordinateGreedyMatching

/- UNCOMPILED. This attempts the genuine native source-bound contract for a
round's actual lower-face predicate. No compiled binder inventory or selector
is guessed. sourceSelection=none is a missing native obligation, not a waiver.
Only the supplied real validator APIs may eventually grant enrollment. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching

namespace Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching
universe u

structure Parameters where
  V : Type u
  dv : DecidableEq V
  F : Finset (Finset V)
  v : V

attribute [instance] Parameters.dv

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
  realize signature (fun _ p a => a ∈ lowers p.F p.v) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [dv : DecidableEq V]
    (F : Finset (Finset V)) (v : V) (a : Finset V),
    R.readout () ⟨V, dv, F, v⟩ a ↔ a ∈ F ∧ v ∉ a ∧ insert v a ∈ F

private theorem bridge : (type_of% (@mem_lowers.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V dv F v a; exact @h V dv F v a
  · intro h V dv F v a; exact @h V dv F v a

private def testParameters : Parameters.{u} where
  V := ULift.{u} Unit
  dv := inferInstance
  F := {∅, {⟨()⟩}}
  v := ⟨()⟩

private theorem present : actual.{u}.readout () testParameters ∅ := by
  apply (mem_lowers _ _ _).mpr
  simp [testParameters]

private theorem absent : ¬ actual.{u}.readout () testParameters {testParameters.v} := by
  intro h
  exact ((mem_lowers _ _ _).mp h).2.1 (Finset.mem_singleton_self _)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.dv testParameters.F testParameters.v ∅
  exact hh.mpr ((mem_lowers _ _ _).mp present)

def family : Registration arena.{u} (type_of% (@mem_lowers.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@mem_lowers.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, ∅, {testParameters.v}, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_lowers.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => a ∈ lowers p.F p.v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCoordinateGreedyMatching
