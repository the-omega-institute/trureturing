import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the projector-product trace identity. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity

open _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the trace coordinate of the product of the two projectors. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun d => Matrix (Fin d) (Fin d) ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)),
    R.readout () d (projector v * projector w) = (‖⟪v, w⟫_ℂ‖ ^ 2 : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0 : EuclideanSpace ℂ (Fin 1)) 0
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠
    Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)
  norm_num

def source_registration : Registration arena (type_of% @trace_projectors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_projectors, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_projectors) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.trace_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.trace_projectors
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
