import D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection

open Filter Real
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation (fixedPriceMinimum)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope (integerInfimum)
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport (theta)
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary (prefixH prefixPrice)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
  (fixed_price_tangent_correction_tendsto)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ _ P => prefixH P * log (prefixH P) *
    (fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) - integerInfimum (Nat.primesLE P)))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun P : ℕ => R.readout () () P) atTop (𝓝 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) := h
  exact one_ne_zero (tendsto_nhds_unique hzero tendsto_const_nhds)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, ?_⟩
  by_contra! same
  have zero : ∀ P : ℕ, actual.readout () () P = 0 := by
    intro P
    rw [← same P]
    simp [actual, realize, prefixH, theta]
  have lim : Tendsto (fun P : ℕ => actual.readout () () P) atTop (𝓝 1) :=
    fixed_price_tangent_correction_tendsto
  have limZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) :=
    lim.congr' (Eventually.of_forall zero)
  exact one_ne_zero (tendsto_nhds_unique limZero tendsto_const_nhds)

def registration : Registration arena (type_of% (@fixed_price_tangent_correction_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_price_tangent_correction_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_price_tangent_correction_tendsto) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection.fixed_price_tangent_correction_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ P => prefixH P * log (prefixH P) *
      (fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) - integerInfimum (Nat.primesLE P)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
