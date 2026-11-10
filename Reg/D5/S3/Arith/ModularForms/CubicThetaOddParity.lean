import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ModularForms.CubicThetaOddParity
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.ModularForms.CubicThetaOddParity
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.ModularForms.CubicThetaOddParity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => PowerSeries.coeff n integralT) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    PowerSeries.coeff (4 * n + 1) integralT = R.readout () () n ∧
    PowerSeries.coeff (4 * n + 3) integralT = 0

private theorem coefficient_zero : PowerSeries.coeff 0 integralT = 1 := by
  have hE : PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℤ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h := PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 0
    rw [show _root_.pentagonal (0 : ℤ) = 0 by decide] at h
    simpa only [Int.coe_negOnePow, Int.natAbs_zero, pow_zero] using h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change PowerSeries.constantCoeff
    ((PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries ℤ)) ^ 3 *
      PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℤ) 1) = 1
  simp only [map_mul, map_pow, PowerSeries.constantCoeff_expand,
    PowerSeries.constantCoeff_invOfUnit, hE]
  norm_num

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hactual := (integralT_coeff_mod_four 0).1
  have hbad := (h 0).1
  norm_num only [Nat.mul_zero, Nat.zero_add] at hactual hbad
  rw [coefficient_zero] at hactual
  change PowerSeries.coeff 1 integralT = 2 at hbad
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 3, ?_⟩
  change PowerSeries.coeff 0 integralT ≠ PowerSeries.coeff 3 integralT
  have hthree := (integralT_coeff_mod_four 0).2
  norm_num only [Nat.mul_zero, Nat.zero_add] at hthree
  rw [coefficient_zero, hthree]
  norm_num

def family : Registration arena (type_of% @integralT_coeff_mod_four) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integralT_coeff_mod_four, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@integralT_coeff_mod_four) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.ModularForms.CubicThetaOddParity.coefficientUnit
  realizationName := `Reg.D5.S3.Arith.ModularForms.CubicThetaOddParity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => PowerSeries.coeff n integralT) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ModularForms.CubicThetaOddParity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.ModularForms.CubicThetaOddParity
end
