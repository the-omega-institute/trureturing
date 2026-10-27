import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage
import Reg.Support.SingleDependentReadout
import Batteries.Tactic.OpenPrivate

/- The original eight telescope binders and all three conclusions are retained.
Only the complete sequence in the first Summable clause is observed. Its
coefficients, both signed logarithmic samples and all prime powers are literal.
The original test family f is the parameter; its index k is the state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage
open LeanInformationAudit Real MeasureTheory Filter Set
open Zeta23.EF
open scoped Topology ComplexConjugate Convolution
open private correlation_bound from D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℕ → ℝ → ℂ) (fun _ => ℕ) (fun _ => ℕ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ f k n =>
    ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
      (weilTest (f k) (f k) (log n) + weilTest (f k) (f k) (-log n)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A : ℝ}, 0 ≤ A → ∀ {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ},
    (∀ k, Continuous (f k)) → Continuous g →
    (∀ k x, ‖f k x‖ ≤ A * exp (-|x|)) →
    (∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x))) →
    (∀ k, Summable (R.readout () f k)) ∧
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
        (weilTest g g (log n) + weilTest g g (-log n))) ∧
    Tendsto (fun k => ∑' n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
        (weilTest (f k) (f k) (log n) + weilTest (f k) (f k) (-log n)))
      atTop (𝓝 (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
          (weilTest g g (log n) + weilTest g g (-log n))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hout := h (A := 0) (by norm_num)
    (f := fun _ _ => (0 : ℂ)) (g := fun _ => (0 : ℂ))
    (fun _ => continuous_const) continuous_const
    (by intro k x; simp) (fun _ => tendsto_const_nhds)
  have hs : Summable (fun _ : ℕ => (1 : ℂ)) := hout.1 0
  have hz : (1 : ℂ) = 0 := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
    hs.tendsto_atTop_zero
  norm_num at hz

private theorem weilTest_eq (f g : ℝ → ℂ) (s : ℝ) :
    weilTest f g s = ∫ x : ℝ, f x * conj (g (x - s)) := by
  simp only [weilTest, convolution_def, ContinuousLinearMap.mul_apply', tilde, neg_sub]

private def exponentialTest (x : ℝ) : ℂ := (exp (-|x|) : ℂ)

private theorem exponentialTest_continuous : Continuous exponentialTest := by
  unfold exponentialTest
  fun_prop

private theorem exponentialTest_bound (x : ℝ) :
    ‖exponentialTest x‖ ≤ (1 : ℝ) * exp (-|x|) := by
  simp [exponentialTest, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

private def dependenceFamily (k : ℕ) : ℝ → ℂ :=
  if k = 0 then (fun _ => 0) else exponentialTest

/-- The actual sensitivity witness lies in the original admitted test domain. -/
private theorem dependenceFamily_admitted :
    (∀ k, Continuous (dependenceFamily k)) ∧
      (∀ k x, ‖dependenceFamily k x‖ ≤ (1 : ℝ) * exp (-|x|)) ∧
      (∀ x, Tendsto (fun k => dependenceFamily k x)
        atTop (𝓝 (exponentialTest x))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · simp only [dependenceFamily, if_pos hk]
      exact continuous_const
    · simpa only [dependenceFamily, if_neg hk] using exponentialTest_continuous
  · intro k x
    by_cases hk : k = 0
    · simp only [dependenceFamily, if_pos hk, norm_zero, one_mul]
      exact (exp_pos _).le
    · simpa only [dependenceFamily, if_neg hk] using exponentialTest_bound x
  · intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    have hk0 : k ≠ 0 := by omega
    simp [dependenceFamily, hk0]

private theorem exponential_correlation_positive (s : ℝ) :
    0 < (weilTest exponentialTest exponentialTest s).re := by
  have hi : Integrable (fun x : ℝ => exp (-|x|) * exp (-|x - s|)) := by
    convert (correlation_bound (A := 1) (by norm_num)
      exponentialTest_continuous exponentialTest_bound s).1.re using 1
    ext x
    simp [exponentialTest]
  have heq : weilTest exponentialTest exponentialTest s =
      ((∫ x : ℝ, exp (-|x|) * exp (-|x - s|) : ℝ) : ℂ) := by
    calc
      _ = ∫ x : ℝ, ((exp (-|x|) * exp (-|x - s|) : ℝ) : ℂ) := by
        rw [weilTest_eq]
        apply integral_congr_ae
        filter_upwards with x
        simp [exponentialTest]
      _ = _ := by rw [integral_complex_ofReal]
  rw [heq, Complex.ofReal_re]
  apply integral_pos_of_integrable_nonneg_nonzero
    (by fun_prop) hi (fun x => (mul_pos (exp_pos _) (exp_pos _)).le) (x := 0)
  exact (mul_pos (exp_pos _) (exp_pos _)).ne'

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨dependenceFamily, 0, 1, ?_⟩
  intro heq
  have hv := congrFun heq 2
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hz (s : ℝ) : weilTest (fun _ : ℝ => (0 : ℂ)) (fun _ => 0) s = 0 := by
    simp [weilTest_eq]
  change
    (((ArithmeticFunction.vonMangoldt 2 / sqrt 2 : ℝ) : ℂ) *
      (weilTest (dependenceFamily 0) (dependenceFamily 0) (log 2) +
        weilTest (dependenceFamily 0) (dependenceFamily 0) (-log 2))) =
    (((ArithmeticFunction.vonMangoldt 2 / sqrt 2 : ℝ) : ℂ) *
      (weilTest (dependenceFamily 1) (dependenceFamily 1) (log 2) +
        weilTest (dependenceFamily 1) (dependenceFamily 1) (-log 2))) at hv
  simp only [dependenceFamily, if_pos rfl, if_neg (by norm_num : (1 : ℕ) ≠ 0),
    hz, zero_add, mul_zero] at hv
  have hcoef : (((ArithmeticFunction.vonMangoldt 2 / sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply div_ne_zero
    · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact hlog.ne'
    · exact (sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hsum : weilTest exponentialTest exponentialTest (log 2) +
      weilTest exponentialTest exponentialTest (-log 2) ≠ 0 := by
    have hp : 0 < (weilTest exponentialTest exponentialTest (log 2) +
        weilTest exponentialTest exponentialTest (-log 2)).re := by
      rw [Complex.add_re]
      exact add_pos (exponential_correlation_positive _) (exponential_correlation_positive _)
    intro h
    exact hp.ne' (by simpa using congrArg Complex.re h)
  exact (mul_ne_zero hcoef hsum) hv.symm

def evidence : Registration arena (type_of% @complete_prime_correlation_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_prime_correlation_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@complete_prime_correlation_tendsto) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage.complete_prime_correlation_tendsto.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f k n =>
    ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
      (weilTest (f k) (f k) (log n) + weilTest (f k) (f k) (-log n)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration_1

end Reg.D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage
