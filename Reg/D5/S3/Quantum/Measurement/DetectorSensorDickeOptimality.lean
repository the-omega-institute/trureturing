import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the public theorems in the mirrored owner. -/

set_option linter.style.longLine false

set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.weight_class_card

namespace Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality

open _root_.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the binomial count at the selected weight. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n k => n.choose k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n k => n.choose k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ,
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (Finset.univ.filter (fun j => x j = true)).card = k)).card = R.readout () n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  change _ = Nat.choose 0 0 + 1 at hb
  rw [weight_class_card] at hb
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 2, ?_⟩
  change Nat.choose 1 0 ≠ Nat.choose 1 2
  norm_num

def source_registration : Registration arena (type_of% @weight_class_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weight_class_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_class_card) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.weight_class_card.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => n.choose k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
