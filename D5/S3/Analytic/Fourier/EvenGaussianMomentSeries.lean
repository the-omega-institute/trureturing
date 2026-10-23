/- GID: D5/S3/Analytic/Fourier/EvenGaussianMomentSeries
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/EvenGaussianMomentSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian domination justifies the even-moment cosine series at every complex argument. -/

import D5.S3.Analytic.Fourier.XiThetaTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
namespace D5.S3.Analytic.Fourier.EvenGaussianMomentSeries
open MeasureTheory ENNReal
open D5.S3.Analytic.Fourier.XiThetaTransform

/-- The normalized even moment of a real signed source. -/
def evenMomentCoefficient (p : ℝ → ℝ) (k : ℕ) : ℝ :=
  (∫ x : ℝ, x ^ (2 * k) * p x) / (2 * k).factorial

private theorem cosh_mul_abs (r x : ℝ) :
    Real.cosh (r * |x|) = Real.cosh (r * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, Real.cosh_neg]

private theorem gaussian_cosh_integrable (C r : ℝ) :
    Integrable (fun x : ℝ => C * Real.exp (-x ^ 2) * Real.cosh (r * |x|)) := by
  have h := ((integrable_tilted_gaussian r).add
    (integrable_tilted_gaussian (-r))).const_mul (C / 2)
  convert h using 1
  ext x
  rw [cosh_mul_abs, Real.cosh_eq]
  simp only [Pi.add_apply, Real.exp_add, neg_mul]
  ring

/-- Gaussian domination permits integration of the complex cosine series term by term.
Neither positivity nor evenness of the real source is required. -/
private theorem hasSum_even_moment_cos {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) (w : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ) * w ^ (2 * k))
      (∫ x : ℝ, (p x : ℂ) * Complex.cos (w * (x : ℂ))) := by
  let F : ℕ → ℝ → ℂ := fun k x =>
    (p x : ℂ) * ((-1 : ℂ) ^ k * (w * (x : ℂ)) ^ (2 * k) / (2 * k).factorial)
  let B : ℕ → ℝ → ℝ := fun k x =>
    C * Real.exp (-x ^ 2) * ((‖w‖ * |x|) ^ (2 * k) / (2 * k).factorial)
  have hseries (x : ℝ) : HasSum (fun k => B k x)
      (C * Real.exp (-x ^ 2) * Real.cosh (‖w‖ * |x|)) :=
    (Real.hasSum_cosh (‖w‖ * |x|)).mul_left _
  have hbint : Integrable (fun x : ℝ => ∑' k, B k x) := by
    have he : (fun x : ℝ => ∑' k, B k x) =
        (fun x : ℝ => C * Real.exp (-x ^ 2) * Real.cosh (‖w‖ * |x|)) :=
      funext (fun x => (hseries x).tsum_eq)
    rw [he]
    exact gaussian_cosh_integrable C ‖w‖
  have hF : HasSum (fun k => ∫ x : ℝ, F k x)
      (∫ x : ℝ, (p x : ℂ) * Complex.cos (w * (x : ℂ))) := by
    apply hasSum_integral_of_dominated_convergence B
    · intro k
      exact ((Complex.continuous_ofReal.comp hp).mul (by fun_prop)).aestronglyMeasurable
    · intro k
      filter_upwards [] with x
      dsimp only [F, B]
      simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (hbound x) (by positivity)
    · filter_upwards [] with x
      exact (hseries x).summable
    · exact hbint
    · filter_upwards [] with x
      exact (Complex.hasSum_cos (w * (x : ℂ))).mul_left (p x : ℂ)
  convert hF using 1
  ext k
  have he : F k = fun x : ℝ =>
      ((-1 : ℂ) ^ k * w ^ (2 * k) / (2 * k).factorial) *
        ((x ^ (2 * k) * p x : ℝ) : ℂ) := by
    ext x
    dsimp only [F]
    push_cast
    rw [mul_pow]
    ring
  rw [he, integral_const_mul, integral_complex_ofReal]
  unfold evenMomentCoefficient
  push_cast
  ring

private theorem abs_even_moment_le (p : ℝ → ℝ) (k : ℕ) :
    |evenMomentCoefficient p k| ≤ evenMomentCoefficient (fun x => |p x|) k := by
  have hh := norm_integral_le_integral_norm (μ := volume)
    (fun x : ℝ => x ^ (2 * k) * p x)
  have he (x : ℝ) : ‖x ^ (2 * k) * p x‖ = x ^ (2 * k) * |p x| := by
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by rw [pow_mul]; positivity : 0 ≤ x ^ (2 * k))]
  simp_rw [he, Real.norm_eq_abs] at hh
  unfold evenMomentCoefficient
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (2 * k).factorial :
    (0 : ℝ) ≤ (2 * k).factorial)]
  exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)

private theorem hasSum_even_moment_cosh {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) {R : ℝ} (hR : 0 ≤ R) :
    HasSum (fun k : ℕ => evenMomentCoefficient p k * R ^ k)
      (∫ x : ℝ, p x * Real.cosh (Real.sqrt R * |x|)) := by
  have hq := hasSum_even_moment_cos hp hbound (Complex.I * (Real.sqrt R : ℂ))
  have hpow (k : ℕ) : (-1 : ℂ) ^ k * (Complex.I * (Real.sqrt R : ℂ)) ^ (2 * k) =
      (R : ℂ) ^ k := by
    rw [pow_mul, ← mul_pow]
    congr 1
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hR]
    ring
  have hcos (x : ℝ) : Complex.cos (Complex.I * (Real.sqrt R : ℂ) * (x : ℂ)) =
      (Real.cosh (Real.sqrt R * |x|) : ℂ) := by
    rw [cosh_mul_abs]
    rw [show Complex.I * (Real.sqrt R : ℂ) * (x : ℂ) =
      ((Real.sqrt R * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.cos_mul_I, Complex.ofReal_cosh]
  have hi : (∫ x : ℝ, (p x : ℂ) *
      Complex.cos (Complex.I * (Real.sqrt R : ℂ) * (x : ℂ))) =
      (((∫ x : ℝ, p x * Real.cosh (Real.sqrt R * |x|)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hcos, Complex.ofReal_mul]
  rw [hi] at hq
  convert Complex.hasSum_re hq using 1
  · ext k
    rw [mul_right_comm, hpow]
    simp [mul_comm, ← Complex.ofReal_pow]

private theorem summable_abs_even_moment {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun k : ℕ => |evenMomentCoefficient p k| * R ^ k) := by
  have hs := (hasSum_even_moment_cosh hp.abs
    (fun x => by simpa only [abs_abs] using hbound x) hR).summable
  exact hs.of_nonneg_of_le (fun k => by positivity)
    (fun k => mul_le_mul_of_nonneg_right (abs_even_moment_le p k) (pow_nonneg hR _))

/-- The explicit integral envelope used for coefficient and uniform tail budgets. -/
def gaussianMomentEnvelope (C R : ℝ) : ℝ :=
  ∫ x : ℝ, C * Real.exp (-x ^ 2) * Real.cosh (Real.sqrt R * |x|)

private theorem absolute_coefficient_envelope {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) {R : ℝ} (hR : 0 ≤ R) :
    (∑' k : ℕ, |evenMomentCoefficient p k| * R ^ k) ≤ gaussianMomentEnvelope C R := by
  have hq := hasSum_even_moment_cosh hp.abs
    (fun x => by simpa only [abs_abs] using hbound x) hR
  have hm := gaussian_cosh_integrable C (Real.sqrt R)
  have hb (x : ℝ) : |p x| * Real.cosh (Real.sqrt R * |x|) ≤
      C * Real.exp (-x ^ 2) * Real.cosh (Real.sqrt R * |x|) :=
    mul_le_mul_of_nonneg_right (hbound x) (Real.cosh_pos _).le
  have hi : Integrable (fun x : ℝ => |p x| * Real.cosh (Real.sqrt R * |x|)) := by
    apply hm.mono' (by fun_prop)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_pos (Real.cosh_pos _)] using hb x
  calc
    _ ≤ ∑' k : ℕ, evenMomentCoefficient (fun x => |p x|) k * R ^ k :=
      (summable_abs_even_moment hp hbound hR).tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_right (abs_even_moment_le p k) (pow_nonneg hR _))
        hq.summable
    _ = _ := hq.tsum_eq
    _ ≤ _ := integral_mono hi hm hb

/-- The square-coordinate cosine transform, defined on the entire complex plane. -/
def cosineSquareTransform (p : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (p x : ℂ) * Complex.cos (Complex.sqrt z * (x : ℂ))

/-- The alternating normalized even-moment series in square coordinates. -/
def evenMomentSeries (p : ℝ → ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k => (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ))

private theorem hasSum_square {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ) * z ^ k)
      (cosineSquareTransform p z) := by
  have h := hasSum_even_moment_cos hp hbound (Complex.sqrt z)
  have hsq : (Complex.sqrt z) ^ 2 = z :=
    Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [pow_mul, hsq, cosineSquareTransform] using h

/-- Gaussian domination gives infinite radius and the actual complex cosine-square function
represented by that series, with absolute coefficient convergence at every radius. -/
private theorem hasFPowerSeries_gaussian {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) :
    (∀ R : ℝ, 0 ≤ R → Summable (fun k : ℕ => |evenMomentCoefficient p k| * R ^ k)) ∧
    HasFPowerSeriesOnBall (cosineSquareTransform p) (evenMomentSeries p) 0 ∞ := by
  have hs := fun R hR => summable_abs_even_moment hp hbound (R := R) hR
  refine ⟨hs, ?_⟩
  have hr : (evenMomentSeries p).radius = ∞ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro r
    simpa [evenMomentSeries, FormalMultilinearSeries.ofScalars_norm,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using hs (r : ℝ) r.coe_nonneg
  refine ⟨by rw [hr], by simp, ?_⟩
  intro z _
  simpa [evenMomentSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
    hasSum_square hp hbound z

private theorem uniform_gaussian_tail {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (N : ℕ) :
    ‖cosineSquareTransform p z - ∑ k ∈ Finset.range N,
      (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ) * z ^ k‖ ≤
      2 * gaussianMomentEnvelope C (2 * R) * (1 / 2 : ℝ) ^ N := by
  have h2R : 0 ≤ 2 * R := by positivity
  have hcoeff (k : ℕ) : |evenMomentCoefficient p k| * (2 * R) ^ k ≤
      gaussianMomentEnvelope C (2 * R) :=
    ((summable_abs_even_moment hp hbound h2R).le_tsum k
      (fun _ _ => by positivity)).trans (absolute_coefficient_envelope hp hbound h2R)
  have hg (k : ℕ) : ‖(-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ) * z ^ k‖ ≤
      gaussianMomentEnvelope C (2 * R) * (1 / 2 : ℝ) ^ k := by
    calc
      _ = |evenMomentCoefficient p k| * ‖z‖ ^ k := by
        simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |evenMomentCoefficient p k| * R ^ k := by gcongr
      _ = (|evenMomentCoefficient p k| * (2 * R) ^ k) * (1 / 2 : ℝ) ^ k := by
        rw [mul_assoc, ← mul_pow]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have h := norm_sub_le_of_geometric_bound_of_hasSum (by norm_num : (1 / 2 : ℝ) < 1)
    hg (hasSum_square hp hbound z) N
  rw [norm_sub_rev] at h
  convert h using 1 <;> ring

private theorem even_moment_jet {p : ℝ → ℝ}
    (hf : HasFPowerSeriesOnBall (cosineSquareTransform p) (evenMomentSeries p) 0 ∞) (k : ℕ) :
    iteratedDeriv k (cosineSquareTransform p) 0 / (k.factorial : ℂ) =
      (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ) := by
  have h := hf.factorial_smul (1 : ℂ) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simp [evenMomentSeries, FormalMultilinearSeries.ofScalars_apply_eq, nsmul_eq_mul] at h
  apply (div_eq_iff (by exact_mod_cast k.factorial_ne_zero : (k.factorial : ℂ) ≠ 0)).2
  exact h.symm.trans (mul_comm _ _)

/-- Complete Gaussian-dominated coefficient bridge: absolute convergence, its integral budget,
an entire scalar power series, all normalized jets, and one explicit tail budget uniform on
each closed disk. Signed sources and the zero source remain in the scope. -/
theorem gaussian_even_moment_series {p : ℝ → ℝ} (hp : Continuous p) {C : ℝ}
    (hbound : ∀ x : ℝ, |p x| ≤ C * Real.exp (-x ^ 2)) :
    (∀ R : ℝ, 0 ≤ R → Summable (fun k : ℕ => |evenMomentCoefficient p k| * R ^ k) ∧
      (∑' k : ℕ, |evenMomentCoefficient p k| * R ^ k) ≤ gaussianMomentEnvelope C R) ∧
    HasFPowerSeriesOnBall (cosineSquareTransform p) (evenMomentSeries p) 0 ∞ ∧
    (∀ k : ℕ, iteratedDeriv k (cosineSquareTransform p) 0 / (k.factorial : ℂ) =
      (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ)) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R → ∀ N : ℕ,
      ‖cosineSquareTransform p z - ∑ k ∈ Finset.range N,
        (-1 : ℂ) ^ k * (evenMomentCoefficient p k : ℂ) * z ^ k‖ ≤
        2 * gaussianMomentEnvelope C (2 * R) * (1 / 2 : ℝ) ^ N) := by
  have hf := (hasFPowerSeries_gaussian hp hbound).2
  exact ⟨fun R hR => ⟨summable_abs_even_moment hp hbound hR,
    absolute_coefficient_envelope hp hbound hR⟩, hf, even_moment_jet hf,
    fun _ hR _ hz N => uniform_gaussian_tail hp hbound hR hz N⟩

end D5.S3.Analytic.Fourier.EvenGaussianMomentSeries
