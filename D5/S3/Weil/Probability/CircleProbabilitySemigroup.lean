/- GID: D5/S3/Weil/Probability/CircleProbabilitySemigroup
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/CircleProbabilitySemigroup
   mirror-E: none(waiver:analytic-proof-source)
   anchors: []
   utility: none
   digest: Realize positive multiplicative Fourier families as unique weakly continuous circle probability convolution semigroups. -/

import D5.S3.Weil.Probability.CircleHerglotzCompletion
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Prod

/-!
The probability measures are constructed from the original Toeplitz matrices.
Their convolution law follows from the product of their actual Fourier moments.
The parameter space is the standard nonnegative real half-line. Positivity of
the exponentiated sequence is an explicit analytic input, not a consequence of
pointwise nonnegative coefficients. No Schoenberg or arithmetic RH theorem is
postulated or relabelled as a conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.CircleProbabilitySemigroup

open MeasureTheory Set
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Probability.CircleHerglotzCompletion
open scoped NNReal MeasureTheory ComplexOrder

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The actual multiplicative convolution has the product of the original
negative-power Fourier moments. -/
theorem circleMoment_mconv (μ ν : Measure Circle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℤ) :
    circleMoment (μ ∗ₘ ν) n = circleMoment μ n * circleMoment ν n := by
  let f : Circle → ℂ := fun z => (z : ℂ) ^ (-n)
  have hf : Continuous f := by
    apply Continuous.zpow₀ continuous_subtype_val
    intro z
    exact Or.inl (Circle.coe_ne_zero z)
  have hprod : Integrable (fun p : Circle × Circle => f p.1 * f p.2) (μ.prod ν) := by
    have hcontinuous : Continuous (fun p : Circle × Circle => f p.1 * f p.2) :=
      (hf.comp continuous_fst).mul (hf.comp continuous_snd)
    simpa using hcontinuous.continuousOn.integrableOn_compact
      (μ := μ.prod ν) isCompact_univ
  change (∫ z, f z ∂(μ ∗ₘ ν)) = (∫ z, f z ∂μ) * ∫ z, f z ∂ν
  rw [Measure.mconv, integral_map (by fun_prop) hf.aestronglyMeasurable]
  have hmul (p : Circle × Circle) : f (p.1 * p.2) = f p.1 * f p.2 := by
    simp only [f, Circle.coe_mul, mul_zpow]
  simp_rw [hmul]
  rw [integral_prod _ hprod]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

/-- Normalized positive Fourier families with continuous time and multiplicative
coefficients have a unique weakly continuous probability realization. Its
identity measure and convolution law are conclusions of the construction. -/
theorem circle_probability_semigroup_of_fourier
    (c : ℝ≥0 → ℤ → ℂ)
    (normalized : ∀ t, c t 0 = 1)
    (initial : ∀ n, c 0 n = 1)
    (multiplicative : ∀ s t n, c (s + t) n = c s n * c t n)
    (timeContinuous : ∀ n, Continuous (fun t => c t n))
    (positive : ∀ t N, (toeplitzMatrix (c t) N).PosSemidef) :
    ∃ μ : ℝ≥0 → ProbabilityMeasure Circle,
      (∀ t n, circleMoment (μ t : Measure Circle) n = c t n) ∧
      Continuous μ ∧
      (μ 0 : Measure Circle) = Measure.dirac 1 ∧
      (∀ s t, (μ (s + t) : Measure Circle) = (μ s : Measure Circle) ∗ₘ (μ t : Measure Circle)) ∧
      (∀ ν : ℝ≥0 → ProbabilityMeasure Circle,
        (∀ t n, circleMoment (ν t : Measure Circle) n = c t n) → ν = μ) := by
  classical
  choose μ hμ using fun t => circle_herglotz_exists (c t) (normalized t) (positive t)
  have hcontinuous : Continuous μ := by
    apply (continuous_iff_circleMoments μ).mpr
    intro n
    simpa only [hμ] using timeContinuous n
  refine ⟨μ, hμ, hcontinuous, ?_, ?_, ?_⟩
  · apply circle_moment_ext
    intro n
    rw [hμ, initial]
    simp [circleMoment]
  · intro s t
    apply circle_moment_ext
    intro n
    rw [hμ, circleMoment_mconv, hμ, hμ, multiplicative]
  · intro ν hν
    funext t
    apply ProbabilityMeasure.toMeasure_injective
    exact circle_moment_ext _ _ (fun n => (hν t n).trans (hμ t n).symm)

/-- All exponential Toeplitz matrices are positive exactly when the prescribed
exponential profile has an actual weakly continuous probability semigroup.
The exponent is arbitrary and its value at zero is the only normalization
hypothesis; symmetry follows from positivity in the forward direction. -/
theorem exponential_toeplitz_iff_probability_semigroup
    (ψ : ℤ → ℝ) (atZero : ψ 0 = 0) :
    (∀ t : ℝ≥0, ∀ N : ℕ,
      (toeplitzMatrix (fun n => (Real.exp (-(t : ℝ) * ψ n) : ℂ)) N).PosSemidef) ↔
    ∃ μ : ℝ≥0 → ProbabilityMeasure Circle,
      (∀ t n, circleMoment (μ t : Measure Circle) n = (Real.exp (-(t : ℝ) * ψ n) : ℂ)) ∧
      Continuous μ ∧
      (μ 0 : Measure Circle) = Measure.dirac 1 ∧
      (∀ s t, (μ (s + t) : Measure Circle) = (μ s : Measure Circle) ∗ₘ (μ t : Measure Circle)) ∧
      (∀ ν : ℝ≥0 → ProbabilityMeasure Circle,
        (∀ t n, circleMoment (ν t : Measure Circle) n = (Real.exp (-(t : ℝ) * ψ n) : ℂ)) → ν = μ) := by
  constructor
  · intro positive
    apply circle_probability_semigroup_of_fourier
      (fun t n => (Real.exp (-(t : ℝ) * ψ n) : ℂ))
    · intro t
      simp [atZero]
    · intro n
      simp
    · intro s t n
      simp only [NNReal.coe_add]
      rw [show -((s : ℝ) + (t : ℝ)) * ψ n = -(s : ℝ) * ψ n + -(t : ℝ) * ψ n by ring,
        Real.exp_add, Complex.ofReal_mul]
    · intro n
      fun_prop
    · exact positive
  · rintro ⟨μ, hμ, _, _, _, _⟩ t N
    have hseq : circleMoment (μ t : Measure Circle) =
        fun n => (Real.exp (-(t : ℝ) * ψ n) : ℂ) := funext (hμ t)
    rw [← hseq]
    exact circle_moment_toeplitz_posSemidef _ N

/-- Any represented real exponential coefficient has a nonnegative exponent.
This is a necessary consequence, not the converse to positive definiteness. -/
theorem exponential_probability_forces_nonnegative
    (ψ : ℤ → ℝ) (μ : ProbabilityMeasure Circle)
    (moments : ∀ n, circleMoment (μ : Measure Circle) n = (Real.exp (-ψ n) : ℂ)) :
    ∀ n, 0 ≤ ψ n := by
  intro n
  have bound : ‖circleMoment (μ : Measure Circle) n‖ ≤ 1 := by
    unfold circleMoment
    calc
      _ ≤ ∫ z : Circle, ‖(z : ℂ) ^ (-n)‖ ∂(μ : Measure Circle) := norm_integral_le_integral_norm _
      _ = 1 := by simp [norm_zpow, Circle.norm_coe]
  rw [moments] at bound
  have hexp : Real.exp (-ψ n) ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using bound
  have h := Real.exp_le_one_iff.mp hexp
  linarith

#print axioms circleMoment_mconv
#print axioms exponential_toeplitz_iff_probability_semigroup
#print axioms exponential_probability_forces_nonnegative

end D5.S3.Weil.Probability.CircleProbabilitySemigroup
