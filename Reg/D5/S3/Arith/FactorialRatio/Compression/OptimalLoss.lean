import D5.S3.Arith.FactorialRatio.Compression.OptimalLoss
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FactorialRatio.Compression.OptimalLoss

open Filter Real
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.Arith.FactorialRatio.Compression.OptimalLoss
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => endpointExcess n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun n : ℕ =>
    log (R.readout () () n : ℝ) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 Real.eulerMascheroniConstant)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa [rejected, realize] using h
  have heq := tendsto_nhds_unique tendsto_const_nhds hz
  linarith [Real.one_half_lt_eulerMascheroniConstant]

def family : Registration arena (type_of% endpoint_loss_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_loss_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 2, ?_⟩
    change endpointExcess 0 ≠ endpointExcess 2
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@endpoint_loss_tendsto) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.OptimalLoss.endpoint_loss_tendsto.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.OptimalLoss.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => endpointExcess n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.OptimalLoss
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.OptimalLoss
