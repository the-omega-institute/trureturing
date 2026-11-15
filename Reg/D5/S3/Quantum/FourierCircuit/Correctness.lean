import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FourierCircuit.Correctness
import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of actual circuit action on all coordinate vectors. -/

namespace Reg.D5.S3.Quantum.FourierCircuit.Correctness
open QuantumAlg QuantumAlg.QuantumFourierTransform.Source
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev Params := Σ oracles : OracleModel, Σ _q : Nat, oracles.Interpretation
abbrev signature : Signature where
  Params := Params
  State p := Fin (2 ^ p.2.1) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (2 ^ p.2.1) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p v => Matrix.mulVec (onBinaryLabels (circuit p.1 p.2.1) p.2.2) v)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (oracles : OracleModel) (q : Nat)
    (environment : oracles.Interpretation) (v : Fin (2 ^ q) → ℂ),
    R.readout () ⟨oracles, q, environment⟩ v =
      QuantumPhaseEstimationGeneral.QFT (2 ^ q) v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := congrFun (h .empty 0 OracleModel.emptyInterpretation (fun _ => 1)) 0
  norm_num [rejected, realize, QuantumPhaseEstimationGeneral.QFT,
    QuantumPhaseEstimationGeneral.scale, QuantumPhaseEstimationGeneral.kernel,
    QuantumPhaseEstimationGeneral.phase] at h0
  exact zero_ne_one h0

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨.empty, 0, OracleModel.emptyInterpretation⟩, (fun _ : Fin (2 ^ 0) => (0 : ℂ)), (fun _ : Fin (2 ^ 0) => (1 : ℂ)), ?_⟩
  intro h
  have h0 := congrFun h (0 : Fin (2 ^ 0))
  change (Matrix.mulVec (onBinaryLabels (circuit .empty 0) OracleModel.emptyInterpretation) (fun _ : Fin (2 ^ 0) => (0 : ℂ))) (0 : Fin (2 ^ 0)) =
    (Matrix.mulVec (onBinaryLabels (circuit .empty 0) OracleModel.emptyInterpretation) (fun _ : Fin (2 ^ 0) => (1 : ℂ))) (0 : Fin (2 ^ 0)) at h0
  simp only [circuit_action] at h0
  norm_num [QuantumPhaseEstimationGeneral.QFT, QuantumPhaseEstimationGeneral.scale,
    QuantumPhaseEstimationGeneral.kernel, QuantumPhaseEstimationGeneral.phase] at h0

def source_registration : Registration arena (type_of% @circuit_action) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circuit_action, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (by cases j; cases i; rfl)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@circuit_action) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.QuantumFourierTransform.Source.circuit_action.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Correctness.source_registration
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
    (fun _ p v => Matrix.mulVec (onBinaryLabels (circuit p.1 p.2.1) p.2.2) v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Correctness
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.FourierCircuit.Correctness
