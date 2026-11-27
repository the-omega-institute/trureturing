/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Positive Laplace mixtures give weighted resolvents for every actual zero occurrence. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Set MeasureTheory
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace

/-- The inverse-log coefficient of the Robin weight in logarithmic coordinates. -/
def H (j u : ℝ) : ℝ := j / u + 1 / u ^ 2

def laplaceWeight (j s v : ℝ) : ℝ := (j + s) * Real.exp (-s * v)

lemma H_nonneg {j u : ℝ} (hj : 0 ≤ j) (hu : 0 < u) : 0 ≤ H j u := by
  unfold H
  positivity

lemma H_antitone {j u v : ℝ} (hj : 0 ≤ j) (hu : 0 < u) (huv : u ≤ v) :
    H j v ≤ H j u := by
  have hv := hu.trans_le huv
  unfold H
  exact add_le_add (div_le_div_of_nonneg_left hj hu huv)
    (div_le_div_of_nonneg_left zero_le_one (by positivity : 0 < u ^ 2)
      (pow_le_pow_left₀ hu.le huv 2))

private lemma laplaceWeight_nonneg {j s v : ℝ} (hj : 0 ≤ j) (hs : 0 ≤ s) :
    0 ≤ laplaceWeight j s v := by
  unfold laplaceWeight
  positivity

private lemma laplaceWeight_eq (j s v : ℝ) : laplaceWeight j s v =
    j * (s ^ (0 : ℕ) * Real.exp (-(v * s))) +
      s ^ (1 : ℕ) * Real.exp (-(v * s)) := by
  unfold laplaceWeight
  rw [show -s * v = -(v * s) by ring]
  ring

lemma laplaceWeight_integrable (j : ℝ) {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun s => laplaceWeight j s v) (Ioi 0) := by
  have h0 := (TwoScaleEndpointMoments.exponential_moment v hv 0).1
  have h1 := (TwoScaleEndpointMoments.exponential_moment v hv 1).1
  apply ((h0.const_mul j).add h1).congr
  filter_upwards with s
  exact (laplaceWeight_eq j s v).symm

/-- Positive Laplace representation, with its full moment normalization. -/
theorem H_eq_laplace (j : ℝ) {v : ℝ} (hv : 0 < v) :
    (∫ s : ℝ in Ioi 0, laplaceWeight j s v) = H j v := by
  have h0 := TwoScaleEndpointMoments.exponential_moment v hv 0
  have h1 := TwoScaleEndpointMoments.exponential_moment v hv 1
  simp_rw [laplaceWeight_eq]
  rw [integral_add (h0.1.const_mul j) h1.1, integral_const_mul, h0.2, h1.2]
  norm_num [H] <;> ring

def denominator (j : ℝ) (z : ℂ) (s : ℝ) : ℂ := (j : ℂ) + s - z

private lemma denominator_re (j : ℝ) (z : ℂ) (s : ℝ) :
    (denominator j z s).re = j + s - z.re := by
  simp [denominator]

lemma denominator_re_pos {j s : ℝ} {z : ℂ} (hj : 1 ≤ j)
    (hs : 0 ≤ s) (hz : z.re < 1) : 0 < (denominator j z s).re := by
  rw [denominator_re]; linarith

lemma denominator_ne {j s : ℝ} {z : ℂ} (hj : 1 ≤ j)
    (hs : 0 ≤ s) (hz : z.re < 1) : denominator j z s ≠ 0 := by
  intro e
  have h := denominator_re_pos hj hs hz
  rw [e, Complex.zero_re] at h
  exact (lt_irrefl _ h)

/-- Moving the real part of the resolvent to the right contracts its ratio. -/
lemma one_sub_div_denominator_norm_le_one {j s : ℝ} {z : ℂ}
    (hj : 1 ≤ j) (hs : 0 ≤ s) (hz : z.re < 1) :
    ‖(1 - z) / denominator j z s‖ ≤ 1 := by
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr (denominator_ne hj hs hz))).mpr
  have hsq : ‖1 - z‖ ^ 2 ≤ ‖denominator j z s‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, zero_sub, denominator, Complex.add_re, Complex.ofReal_re,
      Complex.add_im, Complex.ofReal_im, add_zero]
    have h := mul_nonneg (show 0 ≤ j + s - 1 by linarith)
      (show 0 ≤ j + s + 1 - 2 * z.re by linarith)
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def spectralExp (j : ℝ) (z : ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((z - (j : ℂ)) * (v : ℂ))

private lemma spectralExp_norm (j : ℝ) (z : ℂ) (v : ℝ) :
    ‖spectralExp j z v‖ = Real.exp ((z.re - j) * v) := by
  simp [spectralExp, Complex.norm_exp]

private def modeProduct (j : ℝ) (z : ℂ) (s v : ℝ) : ℂ :=
  (laplaceWeight j s v : ℂ) * spectralExp j z v

private lemma modeProduct_integrable {j : ℝ} {z : ℂ} (hj : 1 ≤ j)
    (hz : z.re < 1) {u : ℝ} (hu : 0 < u) :
    Integrable (fun p : ℝ × ℝ => modeProduct j z p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi u))) := by
  apply (integrable_prod_iff' (by
    exact (show Continuous (fun p : ℝ × ℝ => modeProduct j z p.1 p.2) by
      unfold modeProduct laplaceWeight spectralExp
      fun_prop).aestronglyMeasurable)).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact ((laplaceWeight_integrable j (hu.trans hv)).ofReal.mul_const _)
  · have he : (fun v : ℝ => ∫ s : ℝ in Ioi 0, ‖modeProduct j z s v‖) =ᵐ[
        volume.restrict (Ioi u)] (fun v => H j v * Real.exp ((z.re - j) * v)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      calc
        _ = ∫ s : ℝ in Ioi 0, laplaceWeight j s v * Real.exp ((z.re - j) * v) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          rw [modeProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (laplaceWeight_nonneg (by linarith : 0 ≤ j) hs.le),
            spectralExp_norm]
        _ = _ := by rw [integral_mul_const, H_eq_laplace j (hu.trans hv)]
    have hi : IntegrableOn (fun v : ℝ => H j v * Real.exp ((z.re - j) * v)) (Ioi u) := by
      refine ((integrableOn_exp_mul_Ioi (by linarith : z.re - j < 0) u).const_mul
        (H j u)).mono' ?_ ?_
      · exact (show ContinuousOn (fun v : ℝ => H j v * Real.exp ((z.re - j) * v))
            (Ioi u) by
          intro v hv
          have hv0 : 0 < v := hu.trans hv
          dsimp [H]
          fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (H_nonneg (by linarith : 0 ≤ j) (hu.trans hv)) (Real.exp_nonneg _))]
        exact mul_le_mul_of_nonneg_right (H_antitone (by linarith) hu hv.le)
          (Real.exp_nonneg _)
    exact hi.congr he.symm

private lemma mode_s_integral {j v : ℝ} {z : ℂ} (hv : 0 < v) :
    (∫ s : ℝ in Ioi 0, modeProduct j z s v) = (H j v : ℂ) * spectralExp j z v := by
  dsimp only [modeProduct]
  rw [integral_mul_const]
  rw [integral_complex_ofReal, H_eq_laplace j hv]

def rawResolventKernel (j : ℝ) (z : ℂ) (s u : ℝ) : ℂ :=
  ((j + s : ℝ) : ℂ) * Complex.exp (-(denominator j z s) * (u : ℂ)) /
    denominator j z s

private lemma mode_v_integral {j s : ℝ} {z : ℂ} (hj : 1 ≤ j) (hs : 0 ≤ s)
    (hz : z.re < 1) (u : ℝ) :
    (∫ v : ℝ in Ioi u, modeProduct j z s v) = rawResolventKernel j z s u := by
  have hd : (-denominator j z s).re < 0 := by
    rw [Complex.neg_re]; exact neg_lt_zero.mpr (denominator_re_pos hj hs hz)
  have he : (fun v : ℝ => modeProduct j z s v) =
      fun v : ℝ => ((j + s : ℝ) : ℂ) * Complex.exp (-denominator j z s * (v : ℂ)) := by
    funext v
    unfold modeProduct laplaceWeight spectralExp denominator
    simp only [Complex.ofReal_mul, Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, integral_const_mul, integral_exp_mul_complex_Ioi hd u]
  unfold rawResolventKernel
  simp only [div_neg, neg_div, neg_neg]
  ring

/-- The single complex mode before multiplication by the explicit-formula coefficient. -/
def modeTail (j : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ in Ioi u, (H j v : ℂ) * spectralExp j z v

theorem modeTail_resolvent {j : ℝ} {z : ℂ} (hj : 1 ≤ j) (hz : z.re < 1)
    {u : ℝ} (hu : 0 < u) :
    modeTail j z u = ∫ s : ℝ in Ioi 0, rawResolventKernel j z s u := by
  calc
    modeTail j z u = ∫ v : ℝ in Ioi u, ∫ s : ℝ in Ioi 0, modeProduct j z s v := by
      unfold modeTail
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (mode_s_integral (hu.trans hv)).symm
    _ = ∫ s : ℝ in Ioi 0, ∫ v : ℝ in Ioi u, modeProduct j z s v :=
      (integral_integral_swap (modeProduct_integrable hj hz hu)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mode_v_integral hj hs.le hz u

/-- A mode of the integrated explicit formula Q(exp v). -/
def integratedZeroMode (c z : ℂ) (v : ℝ) : ℂ :=
  -c * Complex.exp ((z - 1) * (v : ℂ))

/-- Its weighted Robin contribution. The coefficient c is kept general. -/
def weightedZeroContribution (j : ℝ) (c z : ℂ) (u : ℝ) : ℂ :=
  -(c * (1 - z)) * modeTail j z u

theorem integratedZeroMode_hasDerivAt (c z : ℂ) (v : ℝ) :
    HasDerivAt (integratedZeroMode c z)
      (c * (1 - z) * Complex.exp ((z - 1) * (v : ℂ))) v := by
  have h := ((((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul
    (z - 1)).cexp).const_mul (-c))
  convert h using 1
  · ext t; simp [integratedZeroMode]
  · norm_num <;> ring

/-- Literal correspondence with the derivative of the individual integrated mode.
The original countable integrated formula permits dominated exchange using its
integrated terms, without differentiating its countable series termwise. -/
theorem weightedZeroContribution_eq_integral_deriv (j : ℝ) (c z : ℂ) (u : ℝ) :
    weightedZeroContribution j c z u =
      ∫ v : ℝ in Ioi u, -(Real.exp ((1 - j) * v) : ℂ) * (H j v : ℂ) *
        deriv (integratedZeroMode c z) v := by
  unfold weightedZeroContribution modeTail
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [(integratedZeroMode_hasDerivAt c z v).deriv]
  unfold spectralExp
  have he : (Real.exp ((1 - j) * v) : ℂ) * Complex.exp ((z - 1) * (v : ℂ)) =
      Complex.exp ((z - (j : ℂ)) * (v : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    congr 1; ring
  rw [← he]
  ring

def mixtureKernel (j : ℝ) (z : ℂ) (s u : ℝ) : ℂ :=
  (laplaceWeight j s u : ℂ) * ((1 - z) / denominator j z s)

theorem weightedZeroContribution_eq_mixture {j : ℝ} {z : ℂ} (hj : 1 ≤ j)
    (hz : z.re < 1) (c : ℂ) {u : ℝ} (hu : 0 < u) :
    weightedZeroContribution j c z u =
      (-c * spectralExp j z u) * (∫ s : ℝ in Ioi 0, mixtureKernel j z s u) := by
  unfold weightedZeroContribution
  rw [modeTail_resolvent hj hz hu]
  simp only [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have he : Complex.exp (-(denominator j z s) * (u : ℂ)) =
      (Real.exp (-s * u) : ℂ) * spectralExp j z u := by
    unfold denominator spectralExp
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    congr 1; ring
  unfold rawResolventKernel mixtureKernel laplaceWeight
  rw [he]
  push_cast
  field_simp [denominator_ne hj hs.le hz]
  <;> ring

lemma mixtureKernel_norm_le {j s : ℝ} {z : ℂ} (hj : 1 ≤ j) (hs : 0 ≤ s)
    (hz : z.re < 1) (u : ℝ) : ‖mixtureKernel j z s u‖ ≤ laplaceWeight j s u := by
  rw [mixtureKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (laplaceWeight_nonneg (by linarith : 0 ≤ j) hs)]
  exact mul_le_of_le_one_right (laplaceWeight_nonneg (by linarith) hs)
    (one_sub_div_denominator_norm_le_one hj hs hz)

/-- Sharp one-mode weighted bound for every real j≥1 and every spectral point
in the open half-plane Re(z)<1. No height or critical-line premise is used. -/
theorem weightedZeroContribution_norm_le {j : ℝ} {z : ℂ} (hj : 1 ≤ j)
    (hz : z.re < 1) (c : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖weightedZeroContribution j c z u‖ ≤
      ‖c‖ * Real.exp ((z.re - j) * u) * H j u := by
  have hi := norm_integral_le_of_norm_le (laplaceWeight_integrable j hu)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mixtureKernel_norm_le hj hs.le hz u)
  rw [H_eq_laplace j hu] at hi
  rw [weightedZeroContribution_eq_mixture hj hz c hu, norm_mul, norm_mul, norm_neg,
    spectralExp_norm]
  exact mul_le_mul_of_nonneg_left hi (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))

/-- Specialization to the exact occurrence indexing in the native formula. -/
def actualWeightedZeroContribution (j : ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  weightedZeroContribution j (actualCoeff k) (actualZero k) u

private lemma actualZero_re_lt_one (k : ℕ) : (actualZero k).re < 1 :=
  (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2

theorem actualWeightedZeroContribution_norm_le {j u : ℝ} (hj : 1 ≤ j)
    (hu : 0 < u) (k : ℕ) : ‖actualWeightedZeroContribution j k u‖ ≤
      ‖actualCoeff k‖ * Real.exp (((actualZero k).re - j) * u) * H j u :=
  weightedZeroContribution_norm_le hj (actualZero_re_lt_one k) (actualCoeff k) hu

theorem actualWeightedZeroContribution_summable {j u : ℝ} (hj : 1 ≤ j)
    (hu : 0 < u) : Summable (fun k => actualWeightedZeroContribution j k u) := by
  apply Summable.of_norm_bounded (actualCoeff_hasSum.summable.norm.mul_right (H j u))
  intro k
  refine (actualWeightedZeroContribution_norm_le hj hu k).trans ?_
  have he : Real.exp (((actualZero k).re - j) * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [actualZero_re_lt_one k]) hu.le
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) he)
    (H_nonneg (by linarith) hu)

/-- The complete spectral sum has the corresponding unconditional majorant. -/
theorem actualWeightedZeroSum_norm_le {j u : ℝ} (hj : 1 ≤ j)
    (hu : 0 < u) :
    ‖∑' k : ℕ, actualWeightedZeroContribution j k u‖ ≤
      ∑' k : ℕ, ‖actualCoeff k‖ * Real.exp (((actualZero k).re - j) * u) * H j u := by
  have hmajor : Summable (fun k : ℕ => ‖actualCoeff k‖ *
      Real.exp (((actualZero k).re - j) * u) * H j u) := by
    apply (actualCoeff_hasSum.summable.norm.mul_right (H j u)).of_nonneg_of_le
    · intro k
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
        (H_nonneg (by linarith) hu)
    · intro k
      have he : Real.exp (((actualZero k).re - j) * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [actualZero_re_lt_one k]) hu.le
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) he)
        (H_nonneg (by linarith) hu)
  exact tsum_of_norm_bounded hmajor.hasSum (actualWeightedZeroContribution_norm_le hj hu)

private lemma coeff_norm_hasSum_of_line
    (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2) :
    HasSum (fun k : ℕ => ‖actualCoeff k‖) firstLiMass := by
  have hn (k : ℕ) : ‖actualCoeff k‖ = (actualCoeff k).re := by
    have hd : actualZero k * (1 - actualZero k) =
        ((1 / 4 + (actualZero k).im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
          hline k] <;> ring
    have hc : actualCoeff k = ((1 / (1 / 4 + (actualZero k).im ^ 2) : ℝ) : ℂ) := by
      simp only [actualCoeff, hd, Complex.ofReal_div, Complex.ofReal_one]
    rw [hc]
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    exact abs_of_pos (one_div_pos.mpr (by positivity))
  simpa only [hn, Complex.ofReal_re] using Complex.hasSum_re actualCoeff_hasSum

/-- On the critical line the sharp bound uses the exact first Li mass. -/
theorem actualWeightedZeroSum_norm_le_of_line {j u : ℝ} (hj : 1 ≤ j)
    (hu : 0 < u) (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2) :
    ‖∑' k : ℕ, actualWeightedZeroContribution j k u‖ ≤
      firstLiMass * Real.exp ((1 / 2 - j) * u) * H j u := by
  have hmass := ((coeff_norm_hasSum_of_line hline).mul_right
    (Real.exp ((1 / 2 - j) * u))).mul_right (H j u)
  apply tsum_of_norm_bounded hmass
  intro k
  simpa only [hline k] using (actualWeightedZeroContribution_norm_le hj hu k)

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
