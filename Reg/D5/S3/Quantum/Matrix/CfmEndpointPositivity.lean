import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CfmEndpointPositivity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.CfmEndpointPositivity
open _root_.D5.S3.Quantum.Matrix.CfmEndpointPositivity
open _root_.D5.S3.Quantum.Matrix.CfmRadialDerivative
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat 3) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ X => X.PosSemidef) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U V : Mat 3), U ∈ cayleyDomain 3 → V ∈ cayleyDomain 3 → U ≤ V →
    R.readout () () (resolventSumDerivative (1/20000 : ℝ) U
      (resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U)) ∧
    R.readout () () (resolventSumDerivative (1/20000 : ℝ) V
      (resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : (0 : Mat 3) ∈ cayleyDomain 3 := by
    exact ⟨by simpa using (Matrix.PosDef.one (n := Fin 3) (R := ℂ)),
      by simpa using (Matrix.PosDef.one (n := Fin 3) (R := ℂ))⟩
  exact (h 0 0 h0 h0 le_rfl).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, -1, ?_⟩
  intro he
  have hz : actual.readout i () 0 := Matrix.PosSemidef.zero
  have hn : (- (1 : Mat 3)).PosSemidef := Eq.mp he hz
  have hd := hn.diag_nonneg (i := 0)
  norm_num at hd

def source_registration : Registration arena (type_of% @endpoint_derivatives_positive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_derivatives_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@endpoint_derivatives_positive) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CfmEndpointPositivity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CfmEndpointPositivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmEndpointPositivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }, {
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Matrix.CfmEndpointPositivity
