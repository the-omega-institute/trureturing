import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverCollapse

/- UNCOMPILED. Observe membership in the exact original-label criticalA face,
including the full q, positivity, embedding and original-index state. The real
CompiledSourceScope/Operands/Contract validators have not been executed.
sourceSelection remains none until the actual compiled probe supplies its raw
owner, binder coordinates and readout path. No audit success is asserted. -/

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse

namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
universe u

structure Parameters where
  V : Type u
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  spokes : Fin (3*q) ↪ V

attribute [instance] Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Fin (3*p.q)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p i => p.spokes i ∈ criticalA p.q p.hq p.spokes)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (i : Fin (3*q)),
    R.readout () ⟨V, dv, q, hq, s⟩ i ↔ i.val+1 = 2 ∨
      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j+1 ∨ i.val+1 = 3*j+2)

private theorem bridge : (type_of% (@criticalA_formula.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V dv q hq s i; exact @h V dv q hq s i
  · intro h V dv q hq s i; exact @h V dv q hq s i

private def testParameters : Parameters.{u} where
  V := ULift.{u} (Fin 3)
  dv := inferInstance
  q := 1
  hq := Nat.zero_lt_one
  spokes := ⟨ULift.up, fun _ _ h => congrArg ULift.down h⟩

private theorem present : actual.{u}.readout () testParameters ⟨1, by omega⟩ := by
  exact (criticalA_formula _ _ _ _).mpr (Or.inl rfl)

private theorem absent : ¬ actual.{u}.readout () testParameters ⟨0, by omega⟩ :=
  criticalA_avoids_zero _ _ _

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h testParameters.V testParameters.dv 1 Nat.zero_lt_one testParameters.spokes ⟨1, by omega⟩
  exact hh.mpr (Or.inl rfl)

def family : Registration arena.{u} (type_of% (@criticalA_formula.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@criticalA_formula.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, ⟨1, by omega⟩, ⟨0, by omega⟩, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@criticalA_formula.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse.family
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
    (fun _ p i => p.spokes i ∈ criticalA p.q p.hq p.spokes) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
