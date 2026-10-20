import D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The rectangular trace-contraction law observes its two distance operands. -/

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance
open scoped BigOperators MatrixOrder ComplexOrder
namespace Reg.D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (T : QuantumChannel a b) (ρ σ : DensityState a),
    r.readout () () (traceDistance (T.mapState ρ) (T.mapState σ)) (traceDistance ρ σ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨T, _⟩ := finite_kraus_quantum_channel
    (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (by simp)
  let ρ : DensityState (Fin 1) := ⟨1, zero_le_one, by norm_num [Matrix.trace, Matrix.diag, Matrix.one_apply]⟩
  exact h T ρ ρ

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  norm_num at hh

def family : Registration arena (type_of% (@trace_contract_rectangular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_contract_rectangular, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trace_contract_rectangular)
    (type_of% (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance.trace_contract_rectangular.__information_unit
  realizationName := `Reg.D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Reg.D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance
