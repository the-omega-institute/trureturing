import D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap

open Filter Real
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation (fixedPriceMinimum)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope (integerInfimum)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
  (fixed_price_tangent_correction_tendsto)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap
  (fixed_price_tangent_correction_log_power_tendsto)
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff (cutoff)
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock (baseCutoff_atTop)
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary (prefixH prefixPrice)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ P => cutoff 2 (prefixPrice P)) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Tendsto (fun P : ℕ =>
    let H := prefixH P
    let L := log H
    let U := R.readout () () P
    let V := fixedPriceMinimum (Nat.primesLE P) (prefixPrice P)
    let I := integerInfimum (Nat.primesLE P)
    L ^ n * (H * L * (V - I) - (1 + 1 / L) * (U ^ 2 / (2 * H)))) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun P : ℕ => prefixH P * log (prefixH P) *
      (fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) - integerInfimum (Nat.primesLE P)))
      atTop (𝓝 0) := by
    simpa only [arena, rejected, realize, pow_zero, one_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_div, mul_zero, sub_zero] using h 0
  exact one_ne_zero (tendsto_nhds_unique fixed_price_tangent_correction_tendsto hzero)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  obtain ⟨P, hP⟩ := (baseCutoff_atTop.eventually_gt_atTop (cutoff 2 (prefixPrice 0))).exists
  exact ⟨(), 0, P, ne_of_lt hP⟩

def family : Registration arena (type_of% (@fixed_price_tangent_correction_log_power_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_price_tangent_correction_log_power_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_price_tangent_correction_log_power_tendsto) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap.fixed_price_tangent_correction_log_power_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "arg", "body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap
