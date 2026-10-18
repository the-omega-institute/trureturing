import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CfmEndpointPositivity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.CfmEndpointPositivity
open _root_.D5.S3.Quantum.Matrix.CfmEndpointPositivity
open _root_.D5.S3.Quantum.Matrix.CfmRadialDerivative
open _root_.D5.S3.Quantum.Matrix.CayleyResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Mat 3) (fun _ => Mat 3) (fun _ => Mat 3)

def actual : Realization signature :=
  realize signature (fun _ U X => resolventSumDerivative (1/20000 : ℝ) U X)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U V : Mat 3), U ∈ cayleyDomain 3 → V ∈ cayleyDomain 3 → U ≤ V →
    (R.readout () U
      (resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U)).PosSemidef ∧
    (resolventSumDerivative (1/20000 : ℝ) V
      (resolventSum (1/20000 : ℝ) V - resolventSum (1/20000 : ℝ) U)).PosSemidef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : (0 : Mat 3) ∈ cayleyDomain 3 := by
    exact ⟨by simpa using (Matrix.PosDef.one (n := Fin 3) (R := ℂ)),
      by simpa using (Matrix.PosDef.one (n := Fin 3) (R := ℂ))⟩
  have hh := (h 0 0 h0 h0 le_rfl).1
  have hn : (- (1 : Mat 3)).PosSemidef := hh
  have hle : (1 : Mat 3) ≤ 0 := neg_nonneg.mp hn.nonneg
  exact one_ne_zero (le_antisymm hle Matrix.PosSemidef.one.nonneg)

private theorem resolvent_zero (s : ℝ) (hs : s ≠ 0) :
    _root_.D5.S3.Quantum.Matrix.CayleyResolvent.resolvent s (0 : Mat 3) =
      s⁻¹ • (1 : Mat 3) := by
  unfold _root_.D5.S3.Quantum.Matrix.CayleyResolvent.resolvent
  rw [sub_zero]
  apply Matrix.inv_eq_right_inv
  simp [smul_mul_smul, hs]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro he
  have hd := congrArg (fun X : Mat 3 => (X 0 0).re) he
  norm_num [actual, realize, resolventSumDerivative, resolventDerivative,
    ContinuousLinearMap.mulLeftRight_apply,
    resolvent_zero 2 (by norm_num), resolvent_zero 3 (by norm_num),
    resolvent_zero 4 (by norm_num), smul_mul_smul] at hd

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
  readout := some (realize signature
    (fun _ U X => resolventSumDerivative (1/20000 : ℝ) U X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CfmEndpointPositivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Matrix.CfmEndpointPositivity
