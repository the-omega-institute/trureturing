import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.BcGhostQuartetCount
import Reg.Support.DependentFamily

/-! Source-faithful actual coefficient readouts, interventions and sensitivity on original Fock. -/

open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostQuartetCount

/-- The two actual coefficient operands, with the original S parameter and Fock state. -/
abbrev coefficientSignature : Signature where
  Params := Finset ℕ
  State _ := Fock
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize _ (fun role S v => if role then (count S : ℂ) * v S else M v S)
    (fun e => nomatch e)

abbrev coefficientArena : Arena where
  signature := coefficientSignature
  Law r := ∀ (v : Fock) (S : Finset ℕ), r.readout false S v = r.readout true S v

def coefficientRejected (i : Bool) : Realization coefficientSignature :=
  realize _ (fun role S v =>
    if role = i then coefficientActual.readout role S v + 1
    else coefficientActual.readout role S v) (fun e => nomatch e)

private theorem coefficientPositive : coefficientArena.Law coefficientActual := M_coefficient

private theorem coefficientNegative (i : Bool) :
    ¬ coefficientArena.Law (coefficientRejected i) := by
  intro h
  have hh := h (ket ∅) ∅
  cases i <;>
    norm_num [coefficientRejected, coefficientActual, realize, M_coefficient, count, ket] at hh

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨∅, 0, ket ∅, ?_⟩
  cases i <;> simp [coefficientActual, realize, M_coefficient, count, ket]

def coefficientFamily : Registration coefficientArena
    (type_of% (@D5.S3.Quantum.Fermionic.BcGhostQuartetCount.M_coefficient)) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨coefficientPositive, coefficientRejected false, coefficientNegative false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected i, ?_, rfl, coefficientNegative i⟩
      intro j hj
      funext S v
      simp [coefficientRejected, realize, hj]
    · intro e
      cases e
  dependence := coefficientDependence

def coefficientAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Quantum.Fermionic.BcGhostQuartetCount.M_coefficient)
    (Realization coefficientSignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostQuartetCount.coefficientUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostQuartetCount.coefficientFamily
  realizationSource := none
  generated := false
  arena := .source ⟨coefficientArena⟩
  objectArena := .source ⟨coefficientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficientArena ⟨coefficientFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature coefficientActual.readout coefficientActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostQuartetCount
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fermionic.BcGhostQuartetCount
