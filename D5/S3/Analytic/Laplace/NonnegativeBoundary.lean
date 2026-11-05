/- GID: D5/S3/Analytic/Laplace/NonnegativeBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/NonnegativeBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonnegative Laplace transform is singular at its finite convergence boundary. -/

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Nonnegative exponential transforms and their convergence boundaries. -/

namespace D5.S3.Analytic.Laplace.NonnegativeBoundary

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section

/-- A holomorphic extension of a positive exponential transform enlarges the
interval on which the defining integral converges. -/
theorem integrable_exp_of_holomorphic_extension {μ : Measure ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) {t r h : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ))
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball (t : ℂ) r))
    (heq : F =ᶠ[𝓝 (t : ℂ)] complexMGF id μ)
    (hh : 0 ≤ h) (hhr : h < r) :
    Integrable (fun x : ℝ => Real.exp ((t + h) * x)) μ := by
  let m : ℕ → ℝ := fun n => ∫ x : ℝ, x ^ n * Real.exp (t * x) ∂μ
  let q : ℕ → ℝ → ℝ := fun n x => h ^ n / (n.factorial : ℝ) *
    (x ^ n * Real.exp (t * x))
  have hq_int (n : ℕ) : Integrable (q n) μ :=
    (integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht n).const_mul _
  have hq_pos (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ q n x := by
    filter_upwards [hpos] with x hx
    dsimp [q]
    positivity
  have hm_pos (n : ℕ) : 0 ≤ m n := by
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    positivity
  have hderiv (n : ℕ) : iteratedDeriv n F (t : ℂ) = (m n : ℂ) := by
    rw [heq.iteratedDeriv_eq n, iteratedDeriv_complexMGF (by simpa using ht)]
    change (∫ x : ℝ, (x : ℂ) ^ n * Complex.exp ((t : ℂ) * x) ∂μ) = _
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_pow]
    simp_rw [← Complex.ofReal_mul]
    exact integral_complex_ofReal (μ := μ)
      (f := fun x : ℝ => x ^ n * Real.exp (t * x))
  have hz : ((t + h : ℝ) : ℂ) ∈ Metric.ball (t : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    exact hhr
  have hseries := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball hF
    hz)
  have hsum : Summable (fun n : ℕ => h ^ n / (n.factorial : ℝ) * m n) := by
    convert hseries.summable using 1
    funext n
    rw [hderiv]
    simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, smul_eq_mul]
    ring
  have hq_integral (n : ℕ) : ∫ x : ℝ, q n x ∂μ =
      h ^ n / (n.factorial : ℝ) * m n := by
    exact integral_const_mul _ _
  have hq_sum (x : ℝ) : HasSum (fun n : ℕ => q n x)
      (Real.exp ((t + h) * x)) := by
    have hexp : HasSum (fun n : ℕ => (h * x) ^ n / (n.factorial : ℝ))
        (Real.exp (h * x)) := by
      simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (h * x)
    have he := hexp.mul_right (Real.exp (t * x))
    convert he using 1
    · funext n
      dsimp [q]
      rw [mul_pow]
      ring
    · rw [← Real.exp_add]
      congr 1
      ring
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, Real.abs_exp]
  have hlin : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp ((t + h) * x)) ∂μ) =
      ∑' n : ℕ, ENNReal.ofReal (h ^ n / (n.factorial : ℝ) * m n) := by
    calc
      _ = ∫⁻ x : ℝ, ∑' n : ℕ, ENNReal.ofReal (q n x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpos] with x hx
        rw [← (hq_sum x).tsum_eq,
          ENNReal.ofReal_tsum_of_nonneg (fun n => by dsimp [q]; positivity) (hq_sum x).summable]
      _ = ∑' n : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal (q n x) ∂μ :=
        lintegral_tsum (fun n => (hq_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ = _ := by
        apply tsum_congr
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hq_int n) (hq_pos n), hq_integral]
  rw [hlin, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (div_nonneg (pow_nonneg hh _) (by positivity)) (hm_pos n)) hsum]
  exact ENNReal.ofReal_lt_top

/-- Holomorphic continuation along a real ray forces the defining positive
exponential integral to converge throughout that ray. -/
theorem integrable_exp_on_real_ray {μ : Measure ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) {a : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hreal : ∀ t : ℝ, t < a → (t : ℂ) ∈ U)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hinit : (integrableExpSet id μ).Nonempty)
    (heq : ∀ t : ℝ, t < a → t ∈ interior (integrableExpSet id μ) →
      F =ᶠ[𝓝 (t : ℂ)] complexMGF id μ) :
    ∀ t : ℝ, t < a → Integrable (fun x : ℝ => Real.exp (t * x)) μ := by
  have hdown {u v : ℝ} (hv : v ∈ integrableExpSet id μ) (huv : u ≤ v) :
      u ∈ integrableExpSet id μ := by
    apply hv.mono' (by fun_prop)
    filter_upwards [hpos] with x hx
    simp only [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hx)
  intro u hua
  by_contra hu
  have hupper (v : ℝ) (hv : v ∈ integrableExpSet id μ) : v ≤ u := by
    by_contra hvu
    exact hu (hdown hv (le_of_lt (lt_of_not_ge hvu)))
  have hb : BddAbove (integrableExpSet id μ) := ⟨u, hupper⟩
  let c : ℝ := sSup (integrableExpSet id μ)
  have hcu : c ≤ u := csSup_le hinit hupper
  have hca : c < a := hcu.trans_lt hua
  have hconv {t : ℝ} (ht : t < c) : t ∈ integrableExpSet id μ := by
    obtain ⟨v, hv, htv⟩ := exists_lt_of_lt_csSup hinit ht
    exact hdown hv htv.le
  obtain ⟨r, hr, hballU⟩ := Metric.isOpen_iff.mp hU (c : ℂ) (hreal c hca)
  let t : ℝ := c - r / 4
  have htc : t < c := by dsimp [t]; linarith
  have ht_int : t ∈ interior (integrableExpSet id μ) := by
    apply mem_interior.mpr
    exact ⟨Iio c, fun v hv => hconv hv, isOpen_Iio, htc⟩
  have hball : Metric.ball (t : ℂ) (r / 2) ⊆ U := by
    intro z hz
    apply hballU
    have hdist : dist (t : ℂ) (c : ℂ) = r / 4 := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      dsimp [t]
      rw [show c - r / 4 - c = -(r / 4) by ring, abs_neg, abs_of_pos (by positivity)]
    have h := dist_triangle z (t : ℂ) (c : ℂ)
    rw [hdist] at h
    have hz' : dist z (t : ℂ) < r / 2 := hz
    change dist z (c : ℂ) < r
    linarith
  have hi := integrable_exp_of_holomorphic_extension hpos ht_int (hF.mono hball)
    (heq t (htc.trans hca) ht_int) (h := r / 3) (by positivity) (by linarith : r / 3 < r / 2)
  have hle : t + r / 3 ≤ c := le_csSup hb hi
  dsimp [t] at hle
  linarith

/-- A positive measure supported on the nonnegative real axis has no
holomorphic continuation across a finite right endpoint of exponential
integrability. -/
theorem nonnegative_exponential_boundary {μ : Measure ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (c : ℝ)
    (hconv : ∀ t : ℝ, t < c → Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hdiv : ∀ t : ℝ, c < t → ¬ Integrable (fun x : ℝ => Real.exp (t * x)) μ) :
    ¬ ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (Metric.ball (c : ℂ) r) ∧
      ∀ z ∈ Metric.ball (c : ℂ) r, z.re < c → F z = complexMGF id μ z := by
  rintro ⟨r, hr, F, hF, heq⟩
  let t : ℝ := c - r / 4
  have ht : t < c := by dsimp [t]; linarith
  have ht_int : t ∈ interior (integrableExpSet id μ) := by
    apply mem_interior.mpr
    refine ⟨Iio c, ?_, isOpen_Iio, ht⟩
    intro u hu
    exact hconv u hu
  have hball : Metric.ball (t : ℂ) (r / 2) ⊆ Metric.ball (c : ℂ) r := by
    intro z hz
    have hdist : dist (t : ℂ) (c : ℂ) = r / 4 := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      dsimp [t]
      rw [show c - r / 4 - c = -(r / 4) by ring, abs_neg, abs_of_pos (by positivity)]
    have h := dist_triangle z (t : ℂ) (c : ℂ)
    rw [hdist] at h
    have hz' : dist z (t : ℂ) < r / 2 := hz
    change dist z (c : ℂ) < r
    linarith
  have hEq : F =ᶠ[𝓝 (t : ℂ)] complexMGF id μ := by
    have htc : (t : ℂ) ∈ Metric.ball (c : ℂ) r :=
      hball (Metric.mem_ball_self (by positivity))
    filter_upwards [(Metric.isOpen_ball.mem_nhds htc),
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show (t : ℂ).re < c by simpa using ht)] with z hz hzc
    exact heq z hz hzc
  have hi := integrable_exp_of_holomorphic_extension hpos ht_int (hF.mono hball)
    hEq (h := r / 3) (by positivity) (by linarith : r / 3 < r / 2)
  exact hdiv (t + r / 3) (by dsimp [t]; linarith) hi

#print axioms integrable_exp_on_real_ray
#print axioms nonnegative_exponential_boundary

end
end D5.S3.Analytic.Laplace.NonnegativeBoundary
