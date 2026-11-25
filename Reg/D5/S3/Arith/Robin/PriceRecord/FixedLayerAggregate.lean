import D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source observations for the two fixed-layer limits of the supported integer infimum. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate

open Filter Real
open scoped BigOperators Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail (activationLayer)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope (integerInfimum)
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport (theta)
open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

namespace Approximation

def actual : Realization signature := realize signature
  (fun _ m P => (prefixH P) ^ (((m : ℝ) - 1) / (m : ℝ)) * log (prefixH P) *
    (integerInfimum (Nat.primesLE P) -
      ∑ j ∈ Finset.Ioc 1 m, ∑ p ∈ Nat.primesLE P,
        min (prefixPrice P * log (p : ℝ)) (1 / (p : ℝ) ^ j)))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 2 ≤ m → Tendsto (fun P : ℕ => R.readout () m P) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := h (m := 2) le_rfl
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hzero)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  obtain ⟨P, hH, hP⟩ := ((prefixH_atTop.eventually_gt_atTop (1 : ℝ)).and
    (eventually_ge_atTop (2 : ℕ))).exists
  have hlog := log_pos hH
  have hscale (m : ℕ) : (prefixH P) ^ (((m : ℝ) - 1) / (m : ℝ)) * log (prefixH P) ≠ 0 :=
    (mul_pos (rpow_pos_of_pos (zero_lt_one.trans hH) _) hlog).ne'
  have hprice : 0 < prefixPrice P := by
    unfold prefixPrice g
    exact one_div_pos.mpr (mul_pos (zero_lt_one.trans hH) hlog)
  have hthird : 0 < activationLayer 3 P := by
    unfold activationLayer
    refine Finset.sum_pos' (fun p hp => ?_) ⟨2, Nat.mem_primesLE.mpr ⟨hP, Nat.prime_two⟩, ?_⟩
    · exact (lt_min (mul_pos hprice (Nat.mem_primesLE.mp hp).2.log_pos)
        (by have := (Nat.mem_primesLE.mp hp).2.pos; positivity)).le
    · exact lt_min (mul_pos hprice Nat.prime_two.log_pos) (by norm_num)
  have h0 (m : ℕ) : actual.readout () m 0 = 0 := by
    simp [actual, realize, prefixH, theta, Nat.primesLE_zero]
  have hsplit :
      (∑ j ∈ Finset.Ioc 1 3, activationLayer j P) =
        (∑ j ∈ Finset.Ioc 1 2, activationLayer j P) + activationLayer 3 P :=
    Finset.sum_Ioc_succ_top (by decide : (1 : ℕ) ≤ 2) (fun j => activationLayer j P)
  by_cases h : actual.readout () 2 P ≠ 0
  · exact ⟨2, P, 0, by simpa only [h0] using h⟩
  have ht : actual.readout () 3 P ≠ 0 := by
    intro ht
    have hzero := not_not.mp h
    change (prefixH P) ^ (((2 : ℕ) - 1 : ℝ) / (2 : ℝ)) * log (prefixH P) *
      (integerInfimum (Nat.primesLE P) - ∑ j ∈ Finset.Ioc 1 2, activationLayer j P) = 0 at hzero
    change (prefixH P) ^ (((3 : ℕ) - 1 : ℝ) / (3 : ℝ)) * log (prefixH P) *
      (integerInfimum (Nat.primesLE P) - ∑ j ∈ Finset.Ioc 1 3, activationLayer j P) = 0 at ht
    have h₂ := (mul_eq_zero.mp hzero).resolve_left (hscale 2)
    have h₃ := (mul_eq_zero.mp ht).resolve_left (hscale 3)
    rw [hsplit] at h₃
    linarith only [h₂, h₃, hthird]
  exact ⟨3, P, 0, by simpa only [h0] using ht⟩

def family : Registration arena (type_of% (@actual_integer_infimum_all_fixed_layers)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_integer_infimum_all_fixed_layers, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_integer_infimum_all_fixed_layers) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate.actual_integer_infimum_all_fixed_layers.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate.Approximation.family
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
    (fun _ m P => (prefixH P) ^ (((m : ℝ) - 1) / (m : ℝ)) * log (prefixH P) *
      (integerInfimum (Nat.primesLE P) -
        ∑ j ∈ Finset.Ioc 1 m, ∑ p ∈ Nat.primesLE P,
          min (prefixPrice P * log (p : ℝ)) (1 / (p : ℝ) ^ j)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Approximation

namespace Residual

def actual : Realization signature := realize signature
  (fun _ m P => prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P *
    (integerInfimum (Nat.primesLE P) - ∑ j ∈ Finset.Ioc 1 (m - 1), activationLayer j P))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 2 ≤ m →
    Tendsto (fun P : ℕ => R.readout () m P) atTop
      (𝓝 (((m : ℝ) / ((m : ℝ) - 1)) * (m : ℝ) ^ (1 / (m : ℝ))))

private theorem limit_ne_zero : (2 / ((2 : ℝ) - 1)) * (2 : ℝ) ^ (1 / (2 : ℝ)) ≠ 0 := by
  have h : 0 < (2 / ((2 : ℝ) - 1)) * (2 : ℝ) ^ (1 / (2 : ℝ)) := by
    norm_num
    positivity
  exact h.ne'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact limit_ne_zero (tendsto_nhds_unique (h (m := 2) le_rfl) tendsto_const_nhds)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨2, 0, ?_⟩
  by_contra! h
  have h0 : actual.readout () 2 0 = 0 := by
    simp [actual, realize, prefixEll, prefixH, theta, Nat.primesLE_zero]
  have hzero := (actual_integer_infimum_fixed_layer_residual (m := 2) le_rfl).congr'
    (Eventually.of_forall (fun P => (h P).symm.trans h0))
  exact limit_ne_zero (tendsto_nhds_unique hzero tendsto_const_nhds)

def family : Registration arena (type_of% (@actual_integer_infimum_fixed_layer_residual)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_integer_infimum_fixed_layer_residual, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_integer_infimum_fixed_layer_residual) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate.actual_integer_infimum_fixed_layer_residual.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate.Residual.family
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
    (fun _ m P => prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P *
      (integerInfimum (Nat.primesLE P) - ∑ j ∈ Finset.Ioc 1 (m - 1), activationLayer j P))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Residual

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
