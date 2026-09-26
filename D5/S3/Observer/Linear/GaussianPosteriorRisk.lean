/- GID: D5/S3/Observer/Linear/GaussianPosteriorRisk
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GaussianPosteriorRisk
   mirror-E: none(waiver:general-gaussian-bayes-risk)
   anchors: []
   digest: Exact extended-valued Bayes risk decomposition, attained minimum and almost-everywhere uniqueness for the actual Gaussian observation law. -/

import D5.S3.Observer.Linear.GaussianObservationDisintegration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
The loss is one half of the Euclidean squared error. Conditional Gaussian
integration is finite at every data value, but the risk of an arbitrary
measurable estimator may be infinite. Global risks therefore use ENNReal
nonnegative integration throughout, not a totalized Bochner integral.

The posterior is the actual regular conditional kernel constructed in
GaussianObservationDisintegration, not an assumed conditional-law certificate.
Measurability is the only restriction on a competing estimator. No global
integrability or finite-risk assumption is imposed on it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.GaussianPosteriorRisk

open MeasureTheory ProbabilityTheory Matrix WithLp
open D5.S3.Observer.Linear.GaussianAffineDisintegration
open D5.S3.Observer.Linear.GaussianObservationPrecision
open D5.S3.Observer.Linear.GaussianObservationDisintegration
open scoped BigOperators ProbabilityTheory ENNReal

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- Euclidean quadratic energy loss, written as a coordinate sum for integration. -/
def energyLoss (x a : E n) : ℝ := (∑ i, (x i - a i)^2) / 2

theorem energyLoss_eq_norm (x a : E n) : energyLoss x a = ‖x - a‖^2 / 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [energyLoss, Real.norm_eq_abs]

theorem energyLoss_nonneg (x a : E n) : 0 ≤ energyLoss x a := by
  unfold energyLoss
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num)

@[simp] theorem energyLoss_self (x : E n) : energyLoss x x = 0 := by
  simp [energyLoss]

@[simp] theorem energyLoss_eq_zero (x a : E n) : energyLoss x a = 0 ↔ x = a := by
  rw [energyLoss_eq_norm]
  simp

@[simp] theorem ofReal_energyLoss_eq_zero (x a : E n) :
    ENNReal.ofReal (energyLoss x a) = 0 ↔ x = a := by
  constructor
  · intro h
    exact (energyLoss_eq_zero x a).mp
      (le_antisymm (ENNReal.ofReal_eq_zero.mp h) (energyLoss_nonneg x a))
  · intro h
    subst a
    simp

private theorem gaussian_coordinate_L2 (m : E n) (S : Matrix n n ℝ) (i : n) :
    MemLp (fun x : E n => x i) 2 (multivariateGaussian m S) := by
  exact ((IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S)).map_fun
    (EuclideanSpace.proj i)).memLp_two

private theorem gaussian_coordinate_mean (m : E n) (S : Matrix n n ℝ) (i : n) :
    ∫ x : E n, x i ∂multivariateGaussian m S = m i := by
  have hi : Integrable (fun x : E n => x) (multivariateGaussian m S) :=
    IsGaussian.integrable_id
  calc
    (∫ x : E n, x i ∂multivariateGaussian m S) =
        (EuclideanSpace.proj i) (∫ x : E n, x ∂multivariateGaussian m S) :=
      (EuclideanSpace.proj i).integral_comp_comm hi
    _ = m i := by rw [integral_id_multivariateGaussian]; rfl

private theorem gaussian_coordinate_square_integrable
    (m : E n) (S : Matrix n n ℝ) (a : E n) (i : n) :
    Integrable (fun x : E n => (x i - a i)^2) (multivariateGaussian m S) :=
  ((gaussian_coordinate_L2 m S i).sub (memLp_const (a i))).integrable_sq

/-- The actual Gaussian integral in one coordinate, including its mean offset. -/
theorem gaussian_coordinate_square (m : E n) (S : Matrix n n ℝ)
    (hS : S.PosSemidef) (a : E n) (i : n) :
    (∫ x : E n, (x i - a i)^2 ∂multivariateGaussian m S) =
      S i i + (m i - a i)^2 := by
  have hL2 := gaussian_coordinate_L2 m S i
  have hm : (∫ x : E n, x i - a i ∂multivariateGaussian m S) = m i - a i := by
    rw [integral_sub (hL2.integrable (by norm_num)) (integrable_const _),
      gaussian_coordinate_mean]
    simp
  have hv := variance_eq_sub (hL2.sub (memLp_const (a i)))
  rw [variance_sub_const hL2.aestronglyMeasurable (a i),
    variance_eval_multivariateGaussian hS i, hm] at hv
  simp only [Pi.pow_apply] at hv
  linarith

/-- Integrability is needed only for the finite conditional Gaussian calculation. -/
theorem gaussian_energy_integrable (m : E n) (S : Matrix n n ℝ) (a : E n) :
    Integrable (fun x => energyLoss x a) (multivariateGaussian m S) := by
  unfold energyLoss
  exact (integrable_finsetSum Finset.univ
    (fun i _ => gaussian_coordinate_square_integrable m S a i)).div_const 2

/-- The expected energy loss under an actual Gaussian probability measure. -/
theorem gaussian_energy_integral (m : E n) (S : Matrix n n ℝ)
    (hS : S.PosSemidef) (a : E n) :
    (∫ x, energyLoss x a ∂multivariateGaussian m S) =
      S.trace / 2 + energyLoss m a := by
  unfold energyLoss
  rw [integral_div, integral_finsetSum _
    (fun i _ => gaussian_coordinate_square_integrable m S a i)]
  simp_rw [gaussian_coordinate_square m S hS a]
  rw [Finset.sum_add_distrib]
  change ((∑ i, S i i) + (∑ i, (m i - a i)^2)) / 2 =
    (∑ i, S i i) / 2 + (∑ i, (m i - a i)^2) / 2
  ring

/-- Nonnegative-integral version, used before integrating over data values. -/
theorem gaussian_energy_lintegral (m : E n) (S : Matrix n n ℝ)
    (hS : S.PosSemidef) (a : E n) :
    (∫⁻ x, ENNReal.ofReal (energyLoss x a) ∂multivariateGaussian m S) =
      ENNReal.ofReal (S.trace / 2) + ENNReal.ofReal (energyLoss m a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_energy_integrable m S a)
    (Filter.Eventually.of_forall (fun x => energyLoss_nonneg x a)),
    gaussian_energy_integral m S hS a,
    ENNReal.ofReal_add (div_nonneg hS.trace_nonneg (by norm_num)) (energyLoss_nonneg m a)]

/-- Global energy risk under the actual data/signal joint law, possibly infinite. -/
def bayesRisk (M : Matrix p n ℝ) (β τ : ℝ) (g : E p → E n) : ℝ≥0∞ :=
  ∫⁻ z : E p × E n, ENNReal.ofReal (energyLoss z.2 (g z.1)) ∂jointLaw M β τ

/-- The attainable finite posterior covariance contribution. -/
def covarianceRisk (M : Matrix p n ℝ) (β τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((covariance M β τ).trace / 2)

/-- Actual deviation from the posterior mean, integrated over the data law. -/
def deviationRisk (M : Matrix p n ℝ) (β τ : ℝ) (g : E p → E n) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (energyLoss (action (gain M β τ) y) (g y)) ∂dataLaw M β τ

/-- Equivalence with averaging the loss directly over the original state/noise input. -/
theorem bayesRisk_input (M : Matrix p n ℝ) (β τ : ℝ) (g : E p → E n)
    (hg : Measurable g) :
    bayesRisk M β τ g = ∫⁻ z,
      ENNReal.ofReal (energyLoss (action signal z) (g (action (observation M) z)))
      ∂inputLaw β τ := by
  have hF : Measurable (fun z : E p × E n => ENNReal.ofReal (energyLoss z.2 (g z.1))) := by
    unfold energyLoss
    fun_prop
  unfold bayesRisk jointLaw
  rw [lintegral_map hF (by fun_prop)]
  rfl

/-- Conditional loss is computed from the identified posterior, not its mode alone. -/
theorem posterior_conditional_loss (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (y : E p) (a : E n) :
    (∫⁻ x, ENNReal.ofReal (energyLoss x a) ∂posteriorKernel M β τ y) =
      covarianceRisk M β τ + ENNReal.ofReal (energyLoss (action (gain M β τ) y) a) := by
  rw [posteriorKernel_eq_candidate]
  unfold candidateLaw covarianceRisk
  rw [gaussian_energy_lintegral _ _ (covariance_posDef M β τ hβ hτ.le).posSemidef a,
    ← gain_eq_center]

/-- Exact Bayes risk decomposition for every measurable estimator, including
infinite-risk estimators. No integrability of g is required. -/
theorem bayesRisk_decomposition (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (g : E p → E n) (hg : Measurable g) :
    bayesRisk M β τ g = covarianceRisk M β τ + deviationRisk M β τ g := by
  have hF : Measurable (fun z : E p × E n => ENNReal.ofReal (energyLoss z.2 (g z.1))) := by
    unfold energyLoss
    fun_prop
  unfold bayesRisk
  rw [posterior_disintegration M β τ hβ hτ, Measure.lintegral_compProd hF]
  simp_rw [posterior_conditional_loss M β τ hβ hτ]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one, deviationRisk]

/-- The actual posterior mean attains the covariance risk. -/
theorem posterior_mean_attains (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    bayesRisk M β τ (action (gain M β τ)) = covarianceRisk M β τ := by
  rw [bayesRisk_decomposition M β τ hβ hτ _ (by fun_prop)]
  simp [deviationRisk]

/-- Global lower bound, with no finite-risk restriction on the competing estimator. -/
theorem posterior_mean_optimal (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (g : E p → E n) (hg : Measurable g) :
    bayesRisk M β τ (action (gain M β τ)) ≤ bayesRisk M β τ g := by
  rw [posterior_mean_attains M β τ hβ hτ, bayesRisk_decomposition M β τ hβ hτ g hg]
  exact le_add_of_nonneg_right (zero_le _)

/-- Zero deviation is equality to the posterior mean almost everywhere in the data. -/
theorem deviationRisk_eq_zero_iff (M : Matrix p n ℝ) (β τ : ℝ)
    (g : E p → E n) (hg : Measurable g) :
    deviationRisk M β τ g = 0 ↔ g =ᵐ[dataLaw M β τ] action (gain M β τ) := by
  have hF : Measurable (fun y : E p =>
      ENNReal.ofReal (energyLoss (action (gain M β τ) y) (g y))) := by
    unfold energyLoss
    fun_prop
  rw [deviationRisk, lintegral_eq_zero_iff' hF.aemeasurable]
  simp only [Filter.EventuallyEq, Pi.zero_apply, ofReal_energyLoss_eq_zero, eq_comm]

/-- Almost-everywhere uniqueness is derived by cancelling a finite covariance risk. -/
theorem posterior_mean_unique (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (g : E p → E n) (hg : Measurable g) :
    bayesRisk M β τ g = covarianceRisk M β τ ↔
      g =ᵐ[dataLaw M β τ] action (gain M β τ) := by
  rw [bayesRisk_decomposition M β τ hβ hτ g hg]
  have hfin : covarianceRisk M β τ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : covarianceRisk M β τ + deviationRisk M β τ g = covarianceRisk M β τ ↔
      deviationRisk M β τ g = 0 := by
    simpa only [add_zero] using
      (ENNReal.add_right_inj hfin : covarianceRisk M β τ + deviationRisk M β τ g =
        covarianceRisk M β τ + 0 ↔ deviationRisk M β τ g = 0)
  rw [hc, deviationRisk_eq_zero_iff M β τ g hg]

/-- Infinite risks remain infinite; they are never totalized to a zero real integral. -/
theorem bayesRisk_eq_top_iff (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (g : E p → E n) (hg : Measurable g) :
    bayesRisk M β τ g = ⊤ ↔ deviationRisk M β τ g = ⊤ := by
  rw [bayesRisk_decomposition M β τ hβ hτ g hg]
  simp [covarianceRisk, ENNReal.add_eq_top]

/-- Any known orthogonal evolution preserves the physical loss exactly. -/
theorem energyLoss_isometry (U : E n ≃ₗᵢ[ℝ] E n) (x a : E n) :
    energyLoss (U x) (U a) = energyLoss x a := by
  rw [energyLoss_eq_norm, energyLoss_eq_norm, ← map_sub, U.norm_map]

/-- Loss for estimating the future state under a specified orthogonal evolution. -/
def futureRisk (M : Matrix p n ℝ) (β τ : ℝ) (U : E n ≃ₗᵢ[ℝ] E n)
    (g : E p → E n) : ℝ≥0∞ :=
  ∫⁻ z : E p × E n, ENNReal.ofReal (energyLoss (U z.2) (g z.1)) ∂jointLaw M β τ

/-- Every future-state estimator corresponds to a present-state estimator by
pulling back through the actual inverse isometry. -/
theorem futureRisk_pullback (M : Matrix p n ℝ) (β τ : ℝ)
    (U : E n ≃ₗᵢ[ℝ] E n) (g : E p → E n) :
    futureRisk M β τ U g = bayesRisk M β τ (fun y => U.symm (g y)) := by
  unfold futureRisk bayesRisk
  apply lintegral_congr_ae
  filter_upwards [] with z
  have h := energyLoss_isometry U z.2 (U.symm (g z.1))
  simpa only [U.apply_symm_apply] using congrArg ENNReal.ofReal h

/-- Transporting the posterior mean is optimal among all measurable future
estimators, with the same minimum risk as at the observation time. -/
theorem futureRisk_lower_bound (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (U : E n ≃ₗᵢ[ℝ] E n)
    (g : E p → E n) (hg : Measurable g) :
    covarianceRisk M β τ ≤ futureRisk M β τ U g := by
  rw [futureRisk_pullback]
  have h := posterior_mean_optimal M β τ hβ hτ
    (fun y => U.symm (g y)) (by fun_prop)
  simpa only [posterior_mean_attains M β τ hβ hτ] using h

/-- Uniform future loss for the transported posterior-mean estimator. -/
theorem transported_mean_risk (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (U : E n ≃ₗᵢ[ℝ] E n) :
    (∫⁻ z : E p × E n, ENNReal.ofReal
      (energyLoss (U z.2) (U (action (gain M β τ) z.1))) ∂jointLaw M β τ) =
      covarianceRisk M β τ := by
  simp_rw [energyLoss_isometry]
  exact posterior_mean_attains M β τ hβ hτ

#print axioms gaussian_energy_integral
#print axioms bayesRisk_decomposition
#print axioms posterior_mean_attains
#print axioms posterior_mean_optimal
#print axioms posterior_mean_unique
#print axioms bayesRisk_eq_top_iff
#print axioms futureRisk_lower_bound
#print axioms transported_mean_risk
end D5.S3.Observer.Linear.GaussianPosteriorRisk
