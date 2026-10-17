import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.CHSHWitness
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumBounds.CHSHWitness
open _root_.D5.S3.QuantumBounds.CHSHWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the product at its right complex operand. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => (Real.sqrt 2 : ℂ)⁻¹ * z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹

theorem rejected_law : ¬ arena.Law rejected := by
  norm_num [arena, rejected, realize]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  change (Real.sqrt 2 : ℂ)⁻¹ * 0 ≠ (Real.sqrt 2 : ℂ)⁻¹ * 1
  rw [mul_zero, mul_one]
  exact Ne.symm (inv_ne_zero hn)

def source_registration : Registration arena (type_of% @complex_sqrt_two_inv_mul_self) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complex_sqrt_two_inv_mul_self, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@complex_sqrt_two_inv_mul_self) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.CHSHWitness.unit
  realizationName := `Reg.D5.S3.QuantumBounds.CHSHWitness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ z => (Real.sqrt 2 : ℂ)⁻¹ * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.CHSHWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.CHSHWitness
