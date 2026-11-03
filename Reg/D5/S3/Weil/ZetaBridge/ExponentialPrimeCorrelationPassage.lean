import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage
import Reg.Support.SingleDependentReadout
import Batteries.Tactic.OpenPrivate

/-! The original eight telescope binders and all three conclusions are retained.
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

private def exponentialTest (x : ℝ) : ℂ := (Real.exp (-|x|) : ℂ)

private theorem exponentialTest_continuous : Continuous exponentialTest := by
  unfold exponentialTest
  fun_prop

private theorem exponentialTest_bound (x : ℝ) :
    ‖exponentialTest x‖ ≤ (1 : ℝ) * exp (-|x|) := by
  simp only [exponentialTest, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, le_refl]

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
    · simp only [dependenceFamily, ite_eq_left hk]
      exact continuous_const
    · simpa only [dependenceFamily, ite_eq_right hk] using exponentialTest_continuous
  · intro k x
    by_cases hk : k = 0
    · simp only [dependenceFamily, ite_eq_left hk, norm_zero, one_mul]
      exact (exp_pos _).le
    · simpa only [dependenceFamily, ite_eq_right hk] using exponentialTest_bound x
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
    simp only [exponentialTest, RCLike.re_eq_complex_re, Complex.conj_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have heq : weilTest exponentialTest exponentialTest s =
      ((∫ x : ℝ, exp (-|x|) * exp (-|x - s|) : ℝ) : ℂ) := by
    calc
      _ = ∫ x : ℝ, ((exp (-|x|) * exp (-|x - s|) : ℝ) : ℂ) := by
        simp only [weilTest, convolution_def, ContinuousLinearMap.mul_apply', tilde, neg_sub]
        apply integral_congr_ae
        filter_upwards with x
        simp only [exponentialTest, Complex.conj_ofReal, Complex.ofReal_mul]
      _ = _ := by rw [integral_complex_ofReal]
  rw [heq, Complex.ofReal_re]
  apply integral_pos_of_integrable_nonneg_nonzero
    (by fun_prop) hi (fun x => (mul_pos (exp_pos _) (exp_pos _)).le) (x := 0)
  exact (mul_pos (exp_pos _) (exp_pos _)).ne'

open private correlation_tendsto from
  D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨hc, hf, hlim⟩ := dependenceFamily_admitted
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcoef : (((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply div_ne_zero
    · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact hlog.ne'
    · exact (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hsum : weilTest exponentialTest exponentialTest (Real.log 2) +
      weilTest exponentialTest exponentialTest (-Real.log 2) ≠ 0 := by
    have hp : 0 < (weilTest exponentialTest exponentialTest (Real.log 2) +
        weilTest exponentialTest exponentialTest (-Real.log 2)).re := by
      rw [Complex.add_re]
      exact add_pos (exponential_correlation_positive _) (exponential_correlation_positive _)
    intro h
    exact hp.ne' (by simpa using congrArg Complex.re h)
  let z : ℂ := ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) *
    (weilTest exponentialTest exponentialTest (Real.log 2) +
      weilTest exponentialTest exponentialTest (-Real.log 2))
  have hz : z ≠ 0 := mul_ne_zero hcoef hsum
  have hsamples : Tendsto (fun k => actual.readout i dependenceFamily k 2)
      atTop (𝓝 z) := by
    change Tendsto (fun k =>
      ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) *
        (weilTest (dependenceFamily k) (dependenceFamily k) (Real.log 2) +
          weilTest (dependenceFamily k) (dependenceFamily k) (-Real.log 2)))
      atTop (𝓝 (((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) *
        (weilTest exponentialTest exponentialTest (Real.log 2) +
          weilTest exponentialTest exponentialTest (-Real.log 2))))
    exact tendsto_const_nhds.mul
      ((correlation_tendsto (A := 1) (g := exponentialTest) (by norm_num)
        hc hf hlim (Real.log 2)).add
        (correlation_tendsto (A := 1) (g := exponentialTest) (by norm_num)
          hc hf hlim (-Real.log 2)))
  have hzero : actual.readout i dependenceFamily 0 2 = 0 := by
    change ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) *
      (weilTest (dependenceFamily 0) (dependenceFamily 0) (Real.log 2) +
        weilTest (dependenceFamily 0) (dependenceFamily 0) (-Real.log 2)) = 0
    simp [dependenceFamily, weilTest, convolution_def,
      ContinuousLinearMap.mul_apply', tilde, neg_sub]
  have hnonzero : ∀ᶠ k in atTop, actual.readout i dependenceFamily k 2 ≠ 0 :=
    hsamples.eventually (eventually_ne_nhds hz)
  obtain ⟨k, hk⟩ := hnonzero.exists
  refine ⟨dependenceFamily, 0, k, ?_⟩
  intro heq
  exact hk ((congrFun heq 2).symm.trans hzero)

def evidence : Registration arena (type_of% @complete_prime_correlation_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_prime_correlation_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@complete_prime_correlation_tendsto) (Realization signature) Unit Unit where
  unitName :=
    Lean.Name.str
      `D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage.complete_prime_correlation_tendsto
      "__information_unit"
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
        "fn", "arg", "body", "fn", "arg"]
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
