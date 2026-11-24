import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A positive Gaussian average acts termwise on an absolutely summable
exponential expansion in the closed critical strip. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace GaussianSpectrumIntegral

private theorem strip_exp_norm_le {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (t : ℝ) :
    ‖Complex.exp (z * (t : ℂ))‖ ≤ 1 + Real.exp t := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  by_cases ht : 0 ≤ t
  · have h := Real.exp_le_exp.mpr (mul_le_of_le_one_left ht hz1)
    linarith
  · have h := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hz0 (le_of_not_ge ht))
    linarith [Real.exp_nonneg t]

/-- Exact Gaussian average of a countable mode expansion. The exponential
moment and absolute convergence justify the interchange uniformly in height. -/
theorem hasSum_gaussian_spectrum {ι : Type*} [Countable ι] {z a : ι → ℂ}
    (hz : ∀ i, 0 ≤ (z i).re ∧ (z i).re ≤ 1) (ha : Summable (fun i => ‖a i‖))
    (T : ℝ) (V : NNReal) :
    HasSum (fun i => a i * Complex.exp (z i * (T : ℂ) + (V : ℂ) * (z i) ^ 2 / 2))
      (∫ t : ℝ, (∑' i, a i * Complex.exp (z i * (t : ℂ))) ∂gaussianReal T V) := by
  let μ := gaussianReal T V
  let f (i : ι) (t : ℝ) := a i * Complex.exp (z i * (t : ℂ))
  let B (i : ι) (t : ℝ) := ‖a i‖ * (1 + Real.exp t)
  have hf (i : ι) : AEStronglyMeasurable (f i) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [f]
    fun_prop
  have hbound (i : ι) : ∀ᵐ t ∂μ, ‖f i t‖ ≤ B i t :=
    ae_of_all _ fun t => by
      unfold f B
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (strip_exp_norm_le (hz i).1 (hz i).2 t) (norm_nonneg _)
  have hs : ∀ᵐ t ∂μ, Summable (fun i => B i t) :=
    ae_of_all _ fun t => ha.mul_right _
  have hexp : Integrable Real.exp μ := by
    simpa only [one_mul] using
      (integrable_exp_mul_gaussianReal (μ := T) (v := V) (1 : ℝ))
  have hB : Integrable (fun t : ℝ => ∑' i, B i t) μ := by
    simp_rw [B, ha.tsum_mul_right]
    exact ((integrable_const (1 : ℝ)).add hexp).const_mul _
  have hlim : ∀ᵐ t ∂μ, HasSum (fun i => f i t) (∑' i, f i t) := by
    filter_upwards [hs, ae_all_iff.2 hbound] with t ht hl
    exact (Summable.of_norm_bounded ht fun i => hl i).hasSum
  have hGaussian := hasSum_integral_of_dominated_convergence B hf hbound hs hB hlim
  have hterm (i : ι) :
      (∫ t : ℝ, f i t ∂μ) =
        a i * Complex.exp (z i * (T : ℂ) + (V : ℂ) * (z i) ^ 2 / 2) := by
    simp only [f, integral_const_mul]
    exact congrArg (a i * ·) (complexMGF_id_gaussianReal (μ := T) (v := V) (z i))
  simpa only [hterm, f, μ] using hGaussian

/-- A weighted Gaussian tail bound obtained by exponential tilting. The same
formula works for upper and lower tails according to the sign of the tilt. -/
theorem weighted_tail {S : Set ℝ} (hS : MeasurableSet S)
    (T : ℝ) (V : NNReal) (r B : ℝ) (hS' : ∀ t ∈ S, B ≤ r * t) :
    (∫ t in S, Real.exp t ∂gaussianReal T V) ≤
      Real.exp ((1 + r) * T + (V : ℝ) * (1 + r) ^ 2 / 2 - B) := by
  let μ := gaussianReal T V
  have hf : Integrable Real.exp μ := by
    simpa only [one_mul] using
      (integrable_exp_mul_gaussianReal (μ := T) (v := V) (1 : ℝ))
  have hg : Integrable (fun t => Real.exp ((1 + r) * t)) μ :=
    integrable_exp_mul_gaussianReal _
  have hmajor : ∀ t ∈ S, Real.exp t ≤ Real.exp (-B) * Real.exp ((1 + r) * t) := by
    intro t ht
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith only [hS' t ht]
  calc
    _ ≤ ∫ t in S, Real.exp (-B) * Real.exp ((1 + r) * t) ∂μ :=
      setIntegral_mono_on hf.integrableOn (hg.const_mul _).integrableOn hS hmajor
    _ ≤ ∫ t, Real.exp (-B) * Real.exp ((1 + r) * t) ∂μ :=
      setIntegral_le_integral (hg.const_mul _)
        (ae_of_all _ fun _ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = _ := by
      rw [integral_const_mul]
      change Real.exp (-B) * mgf (fun x : ℝ => x) (gaussianReal T V) (1 + r) = _
      rw [mgf_fun_id_gaussianReal, ← Real.exp_add]
      congr 1
      ring

/-- On either side of a centered logarithmic window, the weighted tails
are exponentially small under an explicit variance bound. -/
theorem outside_window_exp_bound {T v d a b : ℝ} (hT : 0 < T) (hd : 0 < d) (hd' : d ≤ 1)
    (hv : 0 < v) (hsmall : v ≤ d ^ 2 / 32)
    (ha : a ≤ (1 - d) * T) (hb : (1 + d) * T ≤ b) :
    let V : NNReal := ⟨v * T, (mul_pos hv hT).le⟩
    (∫ t in Set.Iio a, Real.exp t ∂gaussianReal T V) ≤ Real.exp (-2 * T) ∧
      (∫ t in Set.Ioi b, Real.exp t ∂gaussianReal T V) ≤ Real.exp (-2 * T) := by
  dsimp only
  let V : NNReal := ⟨v * T, (mul_pos hv hT).le⟩
  let r := d / (2 * v)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrEq : 2 * v * r = d := by dsimp [r]; field_simp
  have hsmall' : v ≤ 1 / 32 := by
    nlinarith only [hd.le, hd', hsmall, mul_nonneg hd.le (sub_nonneg.mpr hd')]
  have hrs : (v * r) * r = (d / 2) * r := by rw [show v * r = d / 2 by linarith]
  have hrl : d * r ≥ 16 := by
    dsimp [r]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 2 * v by positivity)).mpr
    nlinarith only [hsmall]
  have hql : (1 - r) + v * (1 - r) ^ 2 / 2 + r * (1 - d) ≤ -2 := by
    nlinarith only [hrEq, hrs, hd.le, hsmall', hrl]
  have hqr : (1 + r) + v * (1 + r) ^ 2 / 2 - r * (1 + d) ≤ -2 := by
    nlinarith only [hrEq, hrs, hd', hsmall', hrl]
  constructor
  · refine (weighted_tail measurableSet_Iio T V (-r) (-r * a) ?_).trans ?_
    · intro t ht
      exact mul_le_mul_of_nonpos_left ht.le (neg_nonpos.mpr hr.le)
    · apply Real.exp_le_exp.mpr
      have hbound := mul_le_mul_of_nonneg_left ha hr.le
      have htotal := mul_le_mul_of_nonneg_right hql hT.le
      change (1 + -r) * T + (v * T) * (1 + -r) ^ 2 / 2 - -r * a ≤ -2 * T
      nlinarith only [hbound, htotal]
  · refine (weighted_tail measurableSet_Ioi T V r (r * b) ?_).trans ?_
    · intro t ht
      exact mul_le_mul_of_nonneg_left ht.le hr.le
    · apply Real.exp_le_exp.mpr
      have hbound := mul_le_mul_of_nonneg_left hb hr.le
      have htotal := mul_le_mul_of_nonneg_right hqr hT.le
      change (1 + r) * T + (v * T) * (1 + r) ^ 2 / 2 - r * b ≤ -2 * T
      nlinarith only [hbound, htotal]

end GaussianSpectrumIntegral

#print axioms GaussianSpectrumIntegral.hasSum_gaussian_spectrum
#print axioms GaussianSpectrumIntegral.outside_window_exp_bound
