import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
open _root_.D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the entropy summand at its real argument. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p f => f p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p f => f p - 1) (fun e => nomatch e)

/-- Preserve the two-point entropy inequality and its complete hypothesis telescope. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {u v p q : ℝ} (_hu : 0 ≤ u) (_huv : u < v)
    (_hp : u ≤ p) (_hpv : p ≤ v) (_hs : p + q = u + v),
    Real.negMulLog u + Real.negMulLog v ≤
      R.readout () p Real.negMulLog + Real.negMulLog q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (u := 0) (v := 1) (p := 0) (q := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at bad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena (type_of% @pair_entropy_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pair_entropy_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pair_entropy_le)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a f => f a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
