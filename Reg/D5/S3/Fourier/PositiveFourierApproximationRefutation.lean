import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.PositiveFourierApproximationRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the public sine estimate. -/

namespace Reg.D5.S3.Fourier.PositiveFourierApproximationRefutation

open _root_.D5.S3.Fourier.PositiveFourierApproximationRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n u => |sin (n * u)|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (u : ℝ), R.readout () n u ≤ (n : ℝ) * |sin u|

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, (Real.pi / 2), ?_⟩
  simp only [actual, realize, Nat.cast_one, one_mul, Real.sin_zero,
    Real.sin_pi_div_two, abs_zero, abs_one]
  exact zero_ne_one

def source_registration : Registration arena (type_of% @abs_sin_nat_mul_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨abs_sin_nat_mul_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@abs_sin_nat_mul_le) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.PositiveFourierApproximationRefutation.unit
  realizationName := `Reg.D5.S3.Fourier.PositiveFourierApproximationRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n u => |sin (n * u)|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.PositiveFourierApproximationRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Fourier.PositiveFourierApproximationRefutation
