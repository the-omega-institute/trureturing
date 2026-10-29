/- GID: D5/S3/Analytic/Laplace/NonnegativeContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/NonnegativeContinuation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [mathlib/module/Mathlib.Probability.Moments.ComplexMGF, mathlib/module/Mathlib.Analysis.Complex.TaylorSeries]
   utility: none
   digest: Holomorphic extension of a nonnegative Laplace germ forces new exponential integrability. -/

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace D5.S3.Analytic.Laplace.NonnegativeContinuation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- The positive Taylor coefficients belong to the original transform, while their
convergence comes from the entire extension ball. -/
private theorem mgf_extension {c R t : ℝ} {H : ℂ → ℂ}
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hc : c ∈ interior (integrableExpSet X μ))
    (hH : DifferentiableOn ℂ H (Metric.ball (c : ℂ) R))
    (hgerm : H =ᶠ[𝓝 (c : ℂ)] complexMGF X μ)
    (ht : 0 < t) (htR : t < R) :
    Integrable (fun ω => Real.exp ((c + t) * X ω)) μ ∧
      H ((c + t : ℝ) : ℂ) = (∫ ω, Real.exp ((c + t) * X ω) ∂μ : ℝ) := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    (t ^ n / (n.factorial : ℝ)) * (X ω ^ n * Real.exp (c * X ω))
  have hFint (n : ℕ) : Integrable (F n) μ :=
    (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hc n).const_mul _
  have hFnonneg (n : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ F n ω := by
    filter_upwards [hX] with ω hω
    dsimp [F]
    positivity
  have hderiv (n : ℕ) : iteratedDeriv n H (c : ℂ) =
      ((∫ ω, X ω ^ n * Real.exp (c * X ω) ∂μ : ℝ) : ℂ) := by
    rw [hgerm.iteratedDeriv_eq n]
    have hc' : (c : ℂ).re ∈ interior (integrableExpSet X μ) := by simpa using hc
    rw [iteratedDeriv_complexMGF hc' n]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_exp,
      integral_ofReal]
  have hball : ((c + t : ℝ) : ℂ) ∈ Metric.ball (c : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Real.norm_eq_abs,
      abs_of_pos ht] using htR
  have hseries : HasSum (fun n => ((∫ ω, F n ω ∂μ : ℝ) : ℂ))
      (H ((c + t : ℝ) : ℂ)) := by
    convert Complex.hasSum_taylorSeries_on_ball hH hball using 1
    ext n
    rw [hderiv]
    simp only [F, integral_const_mul, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast, smul_eq_mul]
    push_cast
    ring
  have hreal : Summable (fun n => ∫ ω, F n ω ∂μ) := by
    simpa using (Complex.hasSum_re hseries).summable
  have hpoint (ω : Ω) : HasSum (fun n => F n ω)
      (Real.exp ((c + t) * X ω)) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (t * X ω)).mul_right
      (Real.exp (c * X ω))
    rw [← Real.exp_eq_exp_ℝ] at h
    convert h using 1
    · ext n
      dsimp [F]
      rw [mul_pow]
      ring
    · rw [← Real.exp_add]
      congr 1
      ring
  have hfinite : (∫⁻ ω, ENNReal.ofReal (Real.exp ((c + t) * X ω)) ∂μ) < ∞ := by
    calc
      _ = ∫⁻ ω, ∑' n, ENNReal.ofReal (F n ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hX] with ω hω
        rw [← (hpoint ω).tsum_eq, ENNReal.ofReal_tsum_of_nonneg]
        · intro n
          dsimp [F]
          positivity
        · exact (hpoint ω).summable
      _ = ∑' n, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ :=
        lintegral_tsum (fun n => (hFint n).aemeasurable.ennreal_ofReal)
      _ = ∑' n, ENNReal.ofReal (∫ ω, F n ω ∂μ) := by
        congr 1
        ext n
        exact (ofReal_integral_eq_lintegral_ofReal (hFint n) (hFnonneg n)).symm
      _ < ∞ := hreal.tsum_ofReal_lt_top
  have hint : Integrable (fun ω => Real.exp ((c + t) * X ω)) μ := by
    refine ⟨?_, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (fun ω => (Real.exp_pos _).le))).2 hfinite⟩
    have hXm := aemeasurable_of_mem_interior_integrableExpSet hc
    fun_prop
  refine ⟨hint, ?_⟩
  have hnorm : Summable (fun n => ∫ ω, ‖F n ω‖ ∂μ) := by
    convert hreal using 1
    ext n
    apply integral_congr_ae
    filter_upwards [hFnonneg n] with ω hω
    exact Real.norm_of_nonneg hω
  have hi := hasSum_integral_of_summable_integral_norm hFint hnorm
  have heq : (fun ω => ∑' n, F n ω) = fun ω => Real.exp ((c + t) * X ω) :=
    funext (fun ω => (hpoint ω).tsum_eq)
  rw [heq] at hi
  exact hseries.unique (Complex.hasSum_ofReal.mpr hi)

/-- An actual holomorphic extension of the same nonnegative Laplace germ
forces exponential integrability throughout its real radius. -/
theorem integrable_exp_of_laplace_extension {a R t : ℝ} {H : ℂ → ℂ}
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (ha : -a ∈ interior (integrableExpSet X μ))
    (hH : DifferentiableOn ℂ H (Metric.ball (a : ℂ) R))
    (hgerm : H =ᶠ[𝓝 (a : ℂ)] fun z => complexMGF X μ (-z))
    (ht : 0 < t) (htR : t < R) :
    Integrable (fun ω => Real.exp ((t - a) * X ω)) μ ∧
      H ((a - t : ℝ) : ℂ) = (∫ ω, Real.exp ((t - a) * X ω) ∂μ : ℝ) := by
  have hneg : DifferentiableOn ℂ (fun z => H (-z)) (Metric.ball ((-a : ℝ) : ℂ) R) := by
    intro z hz
    have hz' : -z ∈ Metric.ball (a : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm, ← neg_add, norm_neg] using hz
    exact (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hz')).comp z
      (differentiableAt_id.neg) |>.differentiableWithinAt
  have heq : (fun z => H (-z)) =ᶠ[𝓝 ((-a : ℝ) : ℂ)] complexMGF X μ := by
    have hm : Tendsto (fun z : ℂ => -z) (𝓝 ((-a : ℝ) : ℂ)) (𝓝 (a : ℂ)) := by
      simpa using (continuous_neg.continuousAt (x := ((-a : ℝ) : ℂ))).tendsto
    filter_upwards [hm.eventually hgerm] with z hz
    simpa using hz
  have h := mgf_extension hX ha hneg heq ht htR
  convert h using 1 <;> push_cast <;> congr 1 <;> ring

end D5.S3.Analytic.Laplace.NonnegativeContinuation
