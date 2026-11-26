import D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The prime support on which the minimizer is certified supplies a dependent readout. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock

open Filter Real
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
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

private theorem prefix_price_ratio :
    Tendsto (fun P => prefixPrice P / prefixPrice P) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hP
  have h := one_div_pos.mpr (mul_pos (zero_lt_one.trans hP) (log_pos hP))
  exact (div_self (show prefixPrice P ≠ 0 from
    (show 0 < prefixPrice P from h).ne')).symm

private theorem one_rejected_minimizer (P : ℕ) :
    IsMinimizer (rejected.readout () () P) (prefixPrice P) (fun _ => 1) := by
  simp [rejected, realize, IsMinimizer, supportedAdmissible, linearCost]

private theorem one_clock_zero (P : ℕ) :
    clockIncrement (Nat.primesLE P) (fun _ => 1) / sqrt (prefixH P) = 0 := by
  simp [clockIncrement]

namespace Uniform

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam : ℕ → ℝ},
    Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1) →
    ∀ {l r : ℝ}, l < sqrt 2 → sqrt 2 < r →
    ∀ᶠ P : ℕ in atTop, ∀ a, IsMinimizer (R.readout () () P) (lam P) a →
      l < clockIncrement (Nat.primesLE P) a / sqrt (prefixH P) ∧
      clockIncrement (Nat.primesLE P) a / sqrt (prefixH P) < r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hl : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hr : sqrt (2 : ℝ) < sqrt 2 + 1 := by linarith
  obtain ⟨P, hP⟩ := (h prefix_price_ratio hl hr).exists
  exact (lt_irrefl (0 : ℝ)) (by
    simpa only [one_clock_zero] using (hP (fun _ => 1) (one_rejected_minimizer P)).1)

def family : Registration arena (type_of% (@fixed_price_minimizer_clock_eventually_between)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_price_minimizer_clock_eventually_between, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_price_minimizer_clock_eventually_between) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock.fixed_price_minimizer_clock_eventually_between.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock.Uniform.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "domain", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

namespace Selection

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam : ℕ → ℝ} {a : ℕ → ℕ → ℕ},
    Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1) →
    (∀ᶠ P : ℕ in atTop, IsMinimizer (R.readout () () P) (lam P) (a P)) →
    Tendsto (fun P => clockIncrement (Nat.primesLE P) (a P) / sqrt (prefixH P))
      atTop (𝓝 (sqrt 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (lam := prefixPrice) (a := fun _ _ => 1)
    prefix_price_ratio (Eventually.of_forall one_rejected_minimizer)
  simp only [one_clock_zero] at ht
  exact (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    (tendsto_nhds_unique ht tendsto_const_nhds)

def family : Registration arena (type_of% (@fixed_price_minimizer_clock_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_price_minimizer_clock_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_price_minimizer_clock_tendsto) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock.fixed_price_minimizer_clock_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock.Selection.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg",
        "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Selection

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
