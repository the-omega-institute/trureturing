import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Resources
import D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.ResourcePool
import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.FourierCircuit.Resources
open QuantumAlg QuantumAlg.QuantumFourierTransform.Source
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev Params := Σ oracles : OracleModel, Resource.Event (.quantum FourierGate.model oracles)
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun _ => Nat) (fun _ => Nat)

def actual : Realization signature :=
  realize signature (fun _ p q => ResourcePool.count p.2 (circuit p.1 q).eventCost)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (oracles : OracleModel)
    (event : Resource.Event (.quantum FourierGate.model oracles)) (q : Nat),
    R.readout () ⟨oracles, event⟩ q =
      q * (if .gate .hadamard = event then 1 else 0) +
      q.choose 2 * (if .gate .controlledPhase = event then 1 else 0) +
      (q / 2) * (if .gate .swap = event then 1 else 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h .empty (.gate .hadamard) 1
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨.empty, .gate .hadamard⟩, 0, 1, ?_⟩
  change ResourcePool.count (.gate .hadamard) (circuit .empty 0).eventCost ≠
    ResourcePool.count (.gate .hadamard) (circuit .empty 1).eventCost
  rw [qftSource_circuit_event_count, qftSource_circuit_event_count]
  norm_num

def source_registration : Registration arena (type_of% @qftSource_circuit_event_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@qftSource_circuit_event_count, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@qftSource_circuit_event_count) (Realization signature) Unit Unit := {
  unitName := `QuantumAlg.QuantumFourierTransform.Source.qftSource_circuit_event_count.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FourierCircuit.Resources.source_registration
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
    (fun _ p q => ResourcePool.count p.2 (circuit p.1 q).eventCost)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source.Resources
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end
end Reg.D5.S3.Quantum.FourierCircuit.Resources
