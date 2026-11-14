import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.ShorCountingMarginal
import Reg.Support.SingleDependentReadout

/-! Source-bound normalization audit on the full target-vector readout. -/

namespace Reg.D5.S3.Quantum.ShorCountingMarginal
open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Parameters × ℕ)
    (fun p => Fin p.1.dimension → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => normSquared v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (c : Parameters) (n : ℕ),
    (∑ y : Fin (2 ^ n), R.readout () (c, n) (runQPE c.modularOperator n c.input y)) = 1

private def sample : Parameters := ⟨2, by norm_num, 1, by norm_num, 1, by norm_num⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h sample 0
  norm_num [rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(sample, 0), (fun _ => (0 : ℂ)), fun _ => 1, ?_⟩
  norm_num [actual, realize, normSquared, sample, Parameters.dimension]

def source_registration : Registration arena (type_of% @Parameters.shor_distribution_normalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Parameters.shor_distribution_normalized, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Parameters.shor_distribution_normalized) (Realization signature) Unit Unit := {
  unitName := `QuantumShorOrderFindingCore.Parameters.shor_distribution_normalized.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorCountingMarginal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => normSquared v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorCountingMarginal
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.ShorCountingMarginal
