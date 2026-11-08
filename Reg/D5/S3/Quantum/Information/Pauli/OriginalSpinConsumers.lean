import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
open WithLp
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers

abbrev signature : Signature where
  Params := Bool × E
  State _ := E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p b =>
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD
      (if p.1 then .plus else .minus) p.2 b) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

/-- The varied family occurs only in the original global correspondence hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (opposite : Bool) (D : Relation),
    (∀ a b, D a b = R.readout () (opposite, a) b) →
      Consequences D ∧ MatrixInterfaces opposite D

private def ex : E := (0, ![1, 0, 0])
private def ey : E := (0, ![0, 1, 0])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hnorm : vnorm ey.2 ≤ 1 := by
    norm_num [ey, vnorm,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.vnorm,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot]
  let α : ContractEvaluation :=
    { mass := 1, vector := ey.2, positive := hnorm }
  have hb := (h false (fun _ _ => 0) (fun _ _ => rfl)).1.pb α ex ex ey
  norm_num [
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.PB,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.squareReadout,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.phaseR,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.phaseS,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.evaluate, ex, ey,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.jordan,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(false, ex), 0, ey, ?_⟩
  intro h
  have hz := congrArg (fun a : E => a.2 2) h
  norm_num [actual, realize, ex, ey,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross] at hz

def family : Registration arena (type_of% (@same_D_consequences)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨same_D_consequences, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_D_consequences) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers.same_D_consequences.information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers.family
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
    (fun _ p b =>
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD
        (if p.1 then .plus else .minus) p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "domain", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
