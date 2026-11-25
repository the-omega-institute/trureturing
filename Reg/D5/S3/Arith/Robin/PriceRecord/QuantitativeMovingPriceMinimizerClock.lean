import D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The prime prefix used in the minimizer hypothesis supplies a dependent readout. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock

open Filter Real
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock (IsMinimizer)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster (root_ratio)
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff (cutoff)
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
  (clockIncrement linearCost supportedAdmissible)
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
  (prefixH prefixPrice prefixH_atTop)
open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Finset ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ P => Nat.primesLE P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(), 2, 0, ?_⟩
  change Nat.primesLE 2 ≠ Nat.primesLE 0
  intro h
  have hmem := Nat.mem_primesLE.mpr ⟨le_rfl, Nat.prime_two⟩
  rw [h, Nat.primesLE_zero] at hmem
  exact Finset.notMem_empty _ hmem

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) {C : ℝ} {lam : ℕ → ℝ} {a : ℕ → ℕ → ℕ},
    (∀ᶠ P : ℕ in atTop, |lam P / prefixPrice P - 1| ≤ C / sqrt (prefixH P)) →
    (∀ᶠ P : ℕ in atTop, IsMinimizer (R.readout () () P) (lam P) (a P)) →
    Tendsto (fun P => log (prefixH P) ^ n *
      (clockIncrement (Nat.primesLE P) (a P) - cutoff 2 (prefixPrice P)) /
        sqrt (prefixH P)) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hband : ∀ᶠ P : ℕ in atTop,
      |prefixPrice P / prefixPrice P - 1| ≤ (0 : ℝ) / sqrt (prefixH P) := by
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hP
    have hpos : 0 < prefixPrice P :=
      one_div_pos.mpr (mul_pos (zero_lt_one.trans hP) (log_pos hP))
    simp [div_self hpos.ne']
  have hmin : ∀ᶠ P : ℕ in atTop,
      IsMinimizer (rejected.readout () () P) (prefixPrice P) (fun _ => 1) := by
    exact Filter.Eventually.of_forall fun _ => by
      simp [rejected, realize, IsMinimizer, supportedAdmissible, linearCost]
  have hzero := h 0 hband hmin
  have hcut : Tendsto (fun P => cutoff 2 (prefixPrice P) / sqrt (prefixH P))
      atTop (𝓝 (sqrt 2)) := by
    simpa only [Function.comp_def, sqrt_eq_rpow, prefixPrice, g, referencePrice,
      Nat.cast_ofNat, one_div] using (root_ratio (j := 2) le_rfl).comp prefixH_atTop
  simp only [pow_zero, one_mul, clockIncrement, Nat.cast_one, sub_self, zero_mul,
    Finset.sum_const_zero, zero_sub, neg_div] at hzero
  have hEq := tendsto_nhds_unique hcut (by simpa only [neg_neg, neg_zero] using hzero.neg)
  exact (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' hEq

def family : Registration arena (type_of% (@moving_price_minimizer_clock_log_power_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moving_price_minimizer_clock_log_power_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moving_price_minimizer_clock_log_power_tendsto) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock.moving_price_minimizer_clock_log_power_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => Nat.primesLE P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg",
        "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock
