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

open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance (activationDensity)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock (IsMinimizer)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
  (prefix_minimizers_tangent_bounds tangent_remainder_quadratic)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope (clockIncrement)
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
  (ownPrice tangentRemainder tangent_remainder_nonnegative)
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary (prefixH_atTop)

namespace Curvature

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ H u => tangentRemainder H (H + u)) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {H u : ℝ}, 1 < H → 0 ≤ u →
    activationDensity (H + u) * u ^ 2 / 2 ≤ R.readout () H u ∧
      tangentRemainder H (H + u) ≤ activationDensity H * u ^ 2 / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (H := 2) (u := 0) (by norm_num) le_rfl).1
  norm_num [rejected, realize] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨2, 0, 1, ?_⟩
  change tangentRemainder 2 (2 + 0) ≠ tangentRemainder 2 (2 + 1)
  have hpos : 0 < tangentRemainder 2 (2 + 1) :=
    (tangent_remainder_nonnegative (by norm_num) (by norm_num)).2.mpr (by norm_num)
  simpa [tangentRemainder, add_zero, sub_self] using (ne_of_lt hpos)

def family : Registration arena (type_of% (@tangent_remainder_quadratic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tangent_remainder_quadratic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tangent_remainder_quadratic) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection.tangent_remainder_quadratic.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection.Curvature.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Curvature

namespace Minimizers

def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ a b : ℕ → ℕ → ℕ, ∃ C : ℝ, ∀ᶠ P : ℕ in atTop,
    let S := Nat.primesLE P
    let H := prefixH P
    let η := prefixPrice P
    let lam := ownPrice S (fun p => (b P p : ℝ))
    let gap := R.readout () () P
    (IsMinimizer S η (a P) ∧ IsMinimizer S lam (b P)) ∧
      (0 ≤ clockIncrement S (a P) ∧ 0 ≤ clockIncrement S (b P)) ∧
      (η / η = 1 ∧ |lam / η - 1| ≤ C / sqrt H) ∧
      H * log H * tangentRemainder H (H + clockIncrement S (a P)) ≤ gap ∧
      gap ≤ H * log H * tangentRemainder H (H + clockIncrement S (b P))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨a, b, C, hab⟩
  obtain ⟨P, h, hH⟩ := (hab.and (prefixH_atTop.eventually_gt_atTop 1)).exists
  have hinc := h.2.1.1
  have hT := hH.trans_le (le_add_of_nonneg_right hinc)
  have hrem := (tangent_remainder_nonnegative hH hT).1
  have hpos := mul_nonneg (mul_nonneg (zero_lt_one.trans hH).le (log_pos hH).le) hrem
  have hbad := h.2.2.2.1
  change _ ≤ (-1 : ℝ) at hbad
  exact (by norm_num : ¬ (0 : ℝ) ≤ -1) (hpos.trans hbad)

def family : Registration arena (type_of% (@prefix_minimizers_tangent_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prefix_minimizers_tangent_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_minimizers_tangent_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection.prefix_minimizers_tangent_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection.Minimizers.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "fn", "arg", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Minimizers

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
