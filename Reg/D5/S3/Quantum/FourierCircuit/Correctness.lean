import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FourierCircuit.Correctness
import all D5.S3.Quantum.FourierCircuit.Correctness
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Matrix
import all D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Model
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.FourierCircuit.Correctness
open QuantumAlg QuantumAlg.QuantumFourierTransform.Source
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev Params := Σ oracles : OracleModel, Σ _q : Nat, oracles.Interpretation
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Fin (2 ^ p.2.1) → ℂ) (fun p => Fin (2 ^ p.2.1) → ℂ)

def actual : Realization signature :=
  realize signature
    (fun _ p v => (onBinaryLabels (circuit p.1 p.2.1) p.2.2).applyVec v)
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
  have h0 := congrFun (h .empty 0 .emptyInterpretation (fun _ => 1)) 0
  norm_num [rejected, realize, QuantumPhaseEstimationGeneral.QFT,
    QuantumPhaseEstimationGeneral.scale, QuantumPhaseEstimationGeneral.kernel,
    QuantumPhaseEstimationGeneral.phase] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨.empty, 0, .emptyInterpretation⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have h0 := congrFun h 0
  change (onBinaryLabels (circuit .empty 0) .emptyInterpretation).applyVec (fun _ => 0) 0 =
    (onBinaryLabels (circuit .empty 0) .emptyInterpretation).applyVec (fun _ => 1) 0 at h0
  rw [circuit_action, circuit_action] at h0
  norm_num [QuantumPhaseEstimationGeneral.QFT, QuantumPhaseEstimationGeneral.scale,
    QuantumPhaseEstimationGeneral.kernel, QuantumPhaseEstimationGeneral.phase] at h0

def source_registration : Registration arena (type_of% @circuit_action) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circuit_action, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
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
    (fun _ p v => (onBinaryLabels (circuit p.1 p.2.1) p.2.2).applyVec v)
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
