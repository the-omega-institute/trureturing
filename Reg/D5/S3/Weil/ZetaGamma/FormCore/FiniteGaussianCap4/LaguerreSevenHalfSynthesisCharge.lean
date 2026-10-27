import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge
import Reg.Support.SingleDependentReadout

/-! Dependent-family audit of actual synthesis and central Mellin integration. -/

open FiniteGaussianCap4.LaguerreSevenHalf
open FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit RHGaussianDilationCore

noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge

private theorem basis_integral :
    mellinIntegral (synthesis (lp.single 2 0 (1 : ℝ))) = normalizedCentralMellin 0 := by
  rw [synthesis_mellin_charge]
  simp only [coeffCharge, innerSL_apply_apply, lp.inner_single_right, Real.inner_apply]
  change normalizedCentralMellin 0 *
      ((actualCentralZ 0 / coeffWeight 0) * 1) = normalizedCentralMellin 0
  have h0 : normalizedCentralMellin 0 ≠ 0 := by
    simpa only [Nat.mul_zero] using (normalizedCentralMellin_even_pos 0).ne'
  simp [actualCentralZ, coeffWeight, h0]

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Coeff) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => mellinIntegral (synthesis w)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ w : Coeff, R.readout () () w = normalizedCentralMellin 0 *
    coeffCharge actualCentralChargeVector w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  change (-1 : ℝ) = normalizedCentralMellin 0 * coeffCharge actualCentralChargeVector 0 at h0
  rw [map_zero, mul_zero] at h0
  norm_num at h0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, lp.single 2 0 (1 : ℝ), ?_⟩
  change mellinIntegral (synthesis 0) ≠ mellinIntegral (synthesis (lp.single 2 0 (1 : ℝ)))
  rw [map_zero, map_zero, basis_integral]
  exact Ne.symm (normalizedCentralMellin_even_pos 0).ne'

def family : Registration arena (type_of% synthesis_mellin_charge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨synthesis_mellin_charge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    synthesis_mellin_charge (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge.charge_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge.family
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
    (fun _ _ w => mellinIntegral (synthesis w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge
