/- GID: D5/S3/Arith/Robin/ActualFactorialRobinHighDerivative
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualFactorialRobinHighDerivative
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The actual factorial Robin remainder has a complete fixed-domain high integral with a paid dominated derivative and explicit value and derivative bounds. -/

import D5.S3.Arith.LogConvolutionMassExpansion
import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S3.Arith.Robin.QuotientIntegralBudget
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
N-only source candidate, not a compiler or acceptance receipt.

The actual factorial remainder is the existing arithmetic residual at k(n)=log n,
A=D=1. Its equality with log(floor y)! and its entire high-domain envelope
directly consume the original LogConvolutionMassExpansion suppliers. Their
Terence Tao / immutable Mathlib / Apache attribution stays at the original owner.

The actual Robin scale kernel and its pointwise derivative are consumed at their
original MellinWeightedVariation owner. The entire high-domain majorant and its
integral are consumed at their original QuotientIntegralBudget owner. The seven
required declarations are exposed in place by the matching N visibility candidates;
no implementation is copied or reproved here.

The new content is the dominated derivative of the actual signed high integral on
the complete fixed domain Ioi 1, including a common neighborhood majorant. The
factorial function is not differentiated. No arithmetic harmonic cancellation,
critical signed tail, Robin inequality or RH conclusion is assumed or proved.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative

open D5.S3.Arith.LogConvolutionMassExpansion
  (sum_log_eq_log_factorial floor_factorial_log_error)
open D5.S3.Arith.Robin.MellinWeightedVariation
  (weight scaleWeight scaleDerivative scaleWeight_eq hasDerivAt_scaleWeight)
open D5.S3.Arith.Robin.QuotientIntegralBudget
  (arithmeticPrefix residual mainTerm KernelData measurable_residual
    integrableOn_log_tail integral_log_tail)

/-- The actual factorial remainder, defined through its unique arithmetic prefix. -/
def eta (y : ℝ) : ℝ := residual (fun n : ℕ => Real.log n) 1 1 y

private lemma prefix_log (N : ℕ) :
    (∑ i ∈ Finset.range N, Real.log ((i + 1 : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) := by
  classical
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_Ioc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hi
      omega⟩
  · intro i _ j _ hij
    omega
  · intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    refine ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

private lemma eta_factorial (y : ℝ) :
    eta y = Real.log (⌊y⌋₊.factorial : ℝ) - (y * Real.log y - y) := by
  unfold eta QuotientIntegralBudget.residual mainTerm arithmeticPrefix
  rw [prefix_log, sum_log_eq_log_factorial]
  simp only [one_mul]

/-- The log-prefix instance retains the literal factorial residual. -/
def kernelData : KernelData where
  k n := Real.log n
  C := 1
  mu := 1
  A := 1
  D := 1
  C_nonneg := by norm_num
  mu_nonneg := by norm_num
  coefficient_nonneg n hn := Real.log_nonneg (by exact_mod_cast hn)
  coefficient_le n _ := by simp only [one_mul]; exact le_rfl
  residual_high y hy := by
    change |eta y| ≤ 1 * (1 + Real.log y)
    rw [eta_factorial]
    simpa only [one_mul] using
      floor_factorial_log_error y y (by linarith) le_rfl hy

private lemma eta_high {y : ℝ} (hy : 1 ≤ y) : |eta y| ≤ 1 + Real.log y := by
  simpa only [eta, kernelData, one_mul] using kernelData.residual_high y hy

private lemma eta_measurable : Measurable eta :=
  measurable_residual (fun n : ℕ => Real.log n) 1 1

/-- The original scale kernel normalized by s, at s=exp r. -/
def highKernel (r y : ℝ) : ℝ := Real.exp r * scaleWeight (Real.exp r) y

def highKernelDerivative (r y : ℝ) : ℝ :=
  -((r + Real.log y)⁻¹ ^ 2 + 2 * (r + Real.log y)⁻¹ ^ 3) / y ^ 2

def highIntegrand (r y : ℝ) : ℝ := eta y * highKernel r y

def highIntegrandDerivative (r y : ℝ) : ℝ := eta y * highKernelDerivative r y

/-- The complete actual signed high-domain integral; it is independent of x. -/
def highRemainder (r : ℝ) : ℝ := ∫ y in Ioi (1 : ℝ), highIntegrand r y

def highRemainderDerivative (r : ℝ) : ℝ :=
  ∫ y in Ioi (1 : ℝ), highIntegrandDerivative r y

private lemma highKernel_physical (r y : ℝ) :
    highKernel r y = (Real.exp r) ^ 2 * weight (Real.exp r * y) := by
  rw [highKernel, scaleWeight_eq]
  ring

lemma highKernel_formula {r y : ℝ} (hr : 0 < r) (hy : 1 < y) :
    highKernel r y = ((r + Real.log y)⁻¹ + (r + Real.log y)⁻¹ ^ 2) / y ^ 2 := by
  have hypos : 0 < y := by linarith
  have hden : 0 < r + Real.log y := by positivity [Real.log_pos hy]
  unfold highKernel scaleWeight
  rw [Real.log_mul (Real.exp_ne_zero r) hypos.ne', Real.log_exp]
  field_simp [Real.exp_ne_zero r, hypos.ne', hden.ne']
  <;> ring

private lemma highIntegrand_measurable (r : ℝ) : Measurable (highIntegrand r) := by
  apply eta_measurable.mul
  unfold highKernel scaleWeight
  fun_prop

private lemma highIntegrandDerivative_measurable (r : ℝ) :
    Measurable (highIntegrandDerivative r) := by
  apply eta_measurable.mul
  unfold highKernelDerivative
  fun_prop

private lemma pointwise_derivative {r y : ℝ} (hr : 0 < r) (hy : 1 < y) :
    HasDerivAt (fun q : ℝ => highIntegrand q y) (highIntegrandDerivative r y) r := by
  have hypos : 0 < y := by linarith
  have hden : 0 < r + Real.log y := by positivity [Real.log_pos hy]
  have he : 1 < Real.exp r := Real.one_lt_exp_iff.mpr hr
  have hprod : 1 < Real.exp r * y := by nlinarith [Real.exp_pos r]
  have hexp := Real.hasDerivAt_exp r
  have hscale :=
    (hasDerivAt_scaleWeight (Real.exp_pos r) hypos hprod).comp r hexp
  have hd := (hexp.mul hscale).const_mul (eta y)
  change HasDerivAt (fun q : ℝ => eta y * (Real.exp q * scaleWeight (Real.exp q) y))
    (highIntegrandDerivative r y) r
  have hderiv : eta y *
      (Real.exp r * scaleWeight (Real.exp r) y +
        Real.exp r * (scaleDerivative (Real.exp r) y * Real.exp r)) =
      highIntegrandDerivative r y := by
    unfold highIntegrandDerivative highKernelDerivative scaleWeight scaleDerivative
    rw [Real.log_mul (Real.exp_ne_zero r) hypos.ne', Real.log_exp]
    field_simp [Real.exp_ne_zero r, hypos.ne', hden.ne']
    <;> ring
  exact hd.congr_deriv hderiv

private lemma value_majorant {r y : ℝ} (hr : 0 < r) (hy : 1 < y) :
    |highIntegrand r y| ≤
      (r⁻¹ + r⁻¹ ^ 2) * ((1 + Real.log y) / y ^ 2) := by
  have hypos : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := (Real.log_pos hy).le
  have hden : 0 < r + Real.log y := by linarith
  have hinv : (r + Real.log y)⁻¹ ≤ r⁻¹ := inv_anti₀ hr (by linarith)
  have hnum : (r + Real.log y)⁻¹ + (r + Real.log y)⁻¹ ^ 2 ≤ r⁻¹ + r⁻¹ ^ 2 := by
    gcongr
  have hkpos : 0 ≤ highKernel r y := by
    rw [highKernel_formula hr hy]
    positivity
  rw [highIntegrand, abs_mul, abs_of_nonneg hkpos, highKernel_formula hr hy]
  calc
    _ ≤ (1 + Real.log y) * ((r⁻¹ + r⁻¹ ^ 2) / y ^ 2) :=
      mul_le_mul (eta_high hy.le) (div_le_div_of_nonneg_right hnum (sq_nonneg y))
        (by positivity) (by positivity)
    _ = _ := by ring

private lemma derivative_majorant {a r y : ℝ} (ha : 0 < a) (har : a ≤ r) (hy : 1 < y) :
    |highIntegrandDerivative r y| ≤
      (a⁻¹ ^ 2 + 2 * a⁻¹ ^ 3) * ((1 + Real.log y) / y ^ 2) := by
  have hypos : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := (Real.log_pos hy).le
  have hden : 0 < r + Real.log y := by linarith
  have hinv : (r + Real.log y)⁻¹ ≤ a⁻¹ := inv_anti₀ ha (by linarith)
  have hnum : (r + Real.log y)⁻¹ ^ 2 + 2 * (r + Real.log y)⁻¹ ^ 3 ≤
      a⁻¹ ^ 2 + 2 * a⁻¹ ^ 3 := by
    gcongr
  have habs : |highKernelDerivative r y| =
      ((r + Real.log y)⁻¹ ^ 2 + 2 * (r + Real.log y)⁻¹ ^ 3) / y ^ 2 := by
    unfold highKernelDerivative
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (sq_nonneg y)]
  rw [highIntegrandDerivative, abs_mul, habs]
  calc
    _ ≤ (1 + Real.log y) * ((a⁻¹ ^ 2 + 2 * a⁻¹ ^ 3) / y ^ 2) :=
      mul_le_mul (eta_high hy.le) (div_le_div_of_nonneg_right hnum (sq_nonneg y))
        (by positivity) (by positivity)
    _ = _ := by ring

private lemma value_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (highIntegrand r) (Ioi (1 : ℝ)) := by
  have hm := (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).const_mul
    (r⁻¹ + r⁻¹ ^ 2)
  apply hm.mono' (highIntegrand_measurable r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simpa only [Real.norm_eq_abs] using value_majorant hr hy

private lemma derivative_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (highIntegrandDerivative r) (Ioi (1 : ℝ)) := by
  have hm := (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).const_mul
    (r⁻¹ ^ 2 + 2 * r⁻¹ ^ 3)
  apply hm.mono' (highIntegrandDerivative_measurable r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simpa only [Real.norm_eq_abs] using derivative_majorant hr le_rfl hy

private lemma high_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt highRemainder (highRemainderDerivative r) r := by
  let a : ℝ := r / 2
  let U : Set ℝ := Ioo a (3 * r / 2)
  let B : ℝ → ℝ := fun y => (a⁻¹ ^ 2 + 2 * a⁻¹ ^ 3) *
    ((1 + Real.log y) / y ^ 2)
  have ha : 0 < a := by dsimp [a]; linarith
  have hU : U ∈ 𝓝 r := Ioo_mem_nhds (by dsimp [a]; linarith) (by linarith)
  have hm : Integrable B (volume.restrict (Ioi (1 : ℝ))) :=
    (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).const_mul
      (a⁻¹ ^ 2 + 2 * a⁻¹ ^ 3)
  have hFmeas : ∀ᶠ q in 𝓝 r,
      AEStronglyMeasurable (highIntegrand q) (volume.restrict (Ioi (1 : ℝ))) :=
    Filter.Eventually.of_forall fun q => (highIntegrand_measurable q).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (1 : ℝ))),
      ∀ q ∈ U, ‖highIntegrandDerivative q y‖ ≤ B y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro q hq
    simpa only [B, Real.norm_eq_abs] using derivative_majorant ha hq.1.le hy
  have hdiff : ∀ᵐ y ∂(volume.restrict (Ioi (1 : ℝ))),
      ∀ q ∈ U, HasDerivAt (fun z => highIntegrand z y) (highIntegrandDerivative q y) q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro q hq
    exact pointwise_derivative (ha.trans hq.1) hy
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ))) (F := highIntegrand)
    (F' := highIntegrandDerivative) (bound := B) hU hFmeas (value_integrable hr)
    (highIntegrandDerivative_measurable r).aestronglyMeasurable hbound hm hdiff
  exact h.2

private lemma high_value_bound {r : ℝ} (hr : 0 < r) :
    |highRemainder r| ≤ 2 * (r⁻¹ + r⁻¹ ^ 2) := by
  have hm := (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).const_mul
    (r⁻¹ + r⁻¹ ^ 2)
  calc
    |highRemainder r| ≤ ∫ y in Ioi (1 : ℝ), |highIntegrand r y| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y in Ioi (1 : ℝ), (r⁻¹ + r⁻¹ ^ 2) * ((1 + Real.log y) / y ^ 2) :=
      setIntegral_mono_on (value_integrable hr).abs hm measurableSet_Ioi
        (fun y hy => value_majorant hr hy)
    _ = _ := by
      rw [integral_const_mul, integral_log_tail (by norm_num)]
      simp only [Real.log_one, zero_add, div_one]
      ring

private lemma high_derivative_bound {r : ℝ} (hr : 0 < r) :
    |highRemainderDerivative r| ≤ 2 * (r⁻¹ ^ 2 + 2 * r⁻¹ ^ 3) := by
  have hm := (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 1)).const_mul
    (r⁻¹ ^ 2 + 2 * r⁻¹ ^ 3)
  calc
    |highRemainderDerivative r| ≤ ∫ y in Ioi (1 : ℝ), |highIntegrandDerivative r y| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y in Ioi (1 : ℝ), (r⁻¹ ^ 2 + 2 * r⁻¹ ^ 3) * ((1 + Real.log y) / y ^ 2) :=
      setIntegral_mono_on (derivative_integrable hr).abs hm measurableSet_Ioi
        (fun y hy => derivative_majorant hr le_rfl hy)
    _ = _ := by
      rw [integral_const_mul, integral_log_tail (by norm_num)]
      simp only [Real.log_one, zero_add, div_one]
      ring

/-- The literal factorial remainder and its complete original-weight high integral
have a genuine derivative on every positive log scale, with both full budgets.
No arithmetic cancellation or critical signed estimate is a premise or conclusion. -/
theorem result :
    (∀ y : ℝ, eta y = Real.log (⌊y⌋₊.factorial : ℝ) - (y * Real.log y - y)) ∧
    (∀ r : ℝ, highRemainder r =
      ∫ y in Ioi (1 : ℝ), eta y * ((Real.exp r) ^ 2 * weight (Real.exp r * y))) ∧
    (∀ r : ℝ, 0 < r →
      IntegrableOn (highIntegrand r) (Ioi (1 : ℝ)) ∧
      IntegrableOn (highIntegrandDerivative r) (Ioi (1 : ℝ)) ∧
      HasDerivAt highRemainder (highRemainderDerivative r) r ∧
      |highRemainder r| ≤ 2 * (r⁻¹ + r⁻¹ ^ 2) ∧
      |highRemainderDerivative r| ≤ 2 * (r⁻¹ ^ 2 + 2 * r⁻¹ ^ 3)) := by
  refine ⟨eta_factorial, ?_, ?_⟩
  · intro r
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    rw [highIntegrand, highKernel_physical]
  · intro r hr
    exact ⟨value_integrable hr, derivative_integrable hr, high_hasDerivAt hr,
      high_value_bound hr, high_derivative_bound hr⟩

end D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative

#print axioms D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative.result
