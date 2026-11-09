/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CountableResolvent
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Dominated exchange of a complete countable spectrum through its W-weighted Laplace resolvent. -/

import D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! The W-weight is (v+2)/v^3. Its positive s,v majorant is proved
integrable before per-mode Fubini and the countable dominated exchange.
The existing generic real Laplace moments are reused at rate y. The complete
Robin coefficient theorem uses a different R-weight and is not copied here.
No conjugate identification or removal of occurrences is performed. -/

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent

def R (y : ℝ) : ℝ := (y + 1) / y ^ 2

def W (y : ℝ) : ℝ := (y + 2) / y ^ 3

def laplacePolynomial (s : ℝ) : ℝ := s * (1 + s)

private lemma laplace_moment_integrable {y : ℝ} (hy : 0 < y) (n : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ n * exp (-(y * s))) (Ioi 0) :=
  (TwoScaleEndpointMoments.exponential_moment y hy n).1

private lemma laplace_moment {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (∫ s : ℝ in Ioi 0, s ^ n * exp (-(y * s))) =
      (n.factorial : ℝ) / y ^ (n + 1) :=
  (TwoScaleEndpointMoments.exponential_moment y hy n).2

lemma laplace_weight_integrable {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun s : ℝ => s * (1 + s) * exp (-s * y)) (Ioi 0) := by
  have hi := (laplace_moment_integrable hy 1).add (laplace_moment_integrable hy 2)
  convert hi using 1
  ext s
  simp only [Pi.add_apply]
  rw [show -s * y = -(y * s) by ring]
  ring

private theorem laplace_weight {y : ℝ} (hy : 0 < y) :
    (∫ s : ℝ in Ioi 0, s * (1 + s) * exp (-s * y)) = W y := by
  have he : (fun s : ℝ => s * (1 + s) * exp (-s * y)) =
      (fun s : ℝ => s ^ 1 * exp (-(y * s)) + s ^ 2 * exp (-(y * s))) := by
    funext s
    rw [show -s * y = -(y * s) by ring]
    ring
  rw [he, integral_add (laplace_moment_integrable hy 1) (laplace_moment_integrable hy 2),
    laplace_moment hy 1, laplace_moment hy 2]
  norm_num [W]
  field_simp [hy.ne']
  <;> ring

private lemma R_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt R (-W y) y := by
  change HasDerivAt ((fun x : ℝ => id x + 1) / id ^ 2) (-W y) y
  have hd := ((hasDerivAt_id y).add_const 1).div
    ((hasDerivAt_id y).pow 2) (pow_ne_zero 2 hy.ne')
  convert hd using 1 <;> dsimp [W, Pi.pow_apply] <;> field_simp [hy.ne'] <;> ring

lemma laplacePolynomial_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ laplacePolynomial s := by unfold laplacePolynomial; positivity

lemma W_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ W y := by unfold W; positivity

private lemma R_inverse (y : ℝ) : R y = y⁻¹ + (y⁻¹) ^ 2 := by
  by_cases hy : y = 0
  · simp [hy, R]
  · dsimp [R]; field_simp

private lemma W_inverse (y : ℝ) : W y = (y⁻¹) ^ 2 + 2 * (y⁻¹) ^ 3 := by
  by_cases hy : y = 0
  · simp [hy, W]
  · dsimp [W]; field_simp

private lemma R_tendsto_zero : Tendsto R atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have he : R = fun y : ℝ => y⁻¹ + (y⁻¹) ^ 2 := funext R_inverse
  rw [he]
  simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using h.add (h.pow 2)

lemma W_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : W y ≤ W x := by
  have hy : 0 < y := hx.trans_le hxy
  have hi : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx hxy
  rw [W_inverse, W_inverse]
  exact add_le_add (pow_le_pow_left₀ (inv_nonneg.mpr hy.le) hi 2)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hy.le) hi 3) (by norm_num))

lemma W_tail_integrable {y : ℝ} (hy : 0 < y) : IntegrableOn W (Ioi y) := by
  have h := integrableOn_Ioi_deriv_of_nonpos'
    (fun v (hv : v ∈ Ici y) => R_hasDerivAt (hy.trans_le hv))
    (fun v (hv : v ∈ Ioi y) => neg_nonpos.mpr (W_nonneg (hy.trans hv).le))
    R_tendsto_zero
  exact integrableOn_fun_neg_iff.mp h

private lemma positive_kernel_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ => laplacePolynomial p.1 * exp (-p.1 * p.2))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi y))) := by
  apply (integrable_prod_iff' (by
    exact (show Continuous (fun p : ℝ × ℝ =>
      laplacePolynomial p.1 * exp (-p.1 * p.2)) by
        unfold laplacePolynomial; fun_prop).aestronglyMeasurable)).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact laplace_weight_integrable (hy.trans hv)
  · have he : (fun v : ℝ => ∫ s : ℝ in Ioi 0,
        ‖laplacePolynomial s * exp (-s * v)‖) =ᵐ[volume.restrict (Ioi y)] W := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      calc
        _ = ∫ s : ℝ in Ioi 0, laplacePolynomial s * exp (-s * v) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (laplacePolynomial_nonneg hs.le) (exp_nonneg _))]
        _ = W v := laplace_weight (hy.trans hv)
    exact (W_tail_integrable hy).congr he.symm

structure CountableSpectrum where
  zero : ℕ → ℂ
  coeff : ℕ → ℂ
  strip : ∀ k, 0 < (zero k).re ∧ (zero k).re < 1
  height : ∀ k, 10 < |(zero k).im|
  summable_norm : Summable (fun k => ‖coeff k‖)
  mass_le : (∑' k, ‖coeff k‖) ≤ 2

def denominator (z : ℂ) (s : ℝ) : ℂ := (s : ℂ) + 1 - z

def spectralExp (z : ℂ) (v : ℝ) : ℂ := Complex.exp ((z - 1) * v)

private def modeProduct (z : ℂ) (s v : ℝ) : ℂ :=
  (laplacePolynomial s : ℂ) * (exp (-s * v) : ℂ) * spectralExp z v

def resolventKernel (z : ℂ) (s y : ℝ) : ℂ :=
  (laplacePolynomial s : ℂ) / denominator z s * Complex.exp (-denominator z s * y)

def resolventMode (z : ℂ) (y : ℝ) : ℂ :=
  ∫ s : ℝ in Ioi 0, resolventKernel z s y

def spectralSeries (S : CountableSpectrum) (v : ℝ) : ℂ :=
  ∑' k : ℕ, S.coeff k * spectralExp (S.zero k) v

def spectralTail (S : CountableSpectrum) (y : ℝ) : ℂ :=
  ∫ v : ℝ in Ioi y, (W v : ℂ) * spectralSeries S v

private lemma spectralExp_norm (z : ℂ) (v : ℝ) :
    ‖spectralExp z v‖ = exp ((z.re - 1) * v) := by
  simp [spectralExp, Complex.norm_exp]

private lemma spectralExp_norm_le {z : ℂ} (hz : z.re ≤ 1) {v : ℝ} (hv : 0 ≤ v) :
    ‖spectralExp z v‖ ≤ 1 := by
  rw [spectralExp_norm, exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hv

lemma denominator_norm {z : ℂ} (hz : 10 ≤ |z.im|) (s : ℝ) :
    10 ≤ ‖denominator z s‖ := by
  exact hz.trans (by simpa [denominator] using
    Complex.abs_im_le_norm ((s : ℂ) + 1 - z))

lemma denominator_ne {z : ℂ} (hz : 10 ≤ |z.im|) (s : ℝ) :
    denominator z s ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (denominator_norm hz s))

private lemma modeProduct_bound {z : ℂ} (hz : z.re ≤ 1) {s v : ℝ}
    (hs : 0 ≤ s) (hv : 0 ≤ v) :
    ‖modeProduct z s v‖ ≤ laplacePolynomial s * exp (-s * v) := by
  rw [modeProduct, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (laplacePolynomial_nonneg hs), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right
    (mul_nonneg (laplacePolynomial_nonneg hs) (exp_nonneg _)) (spectralExp_norm_le hz hv)

private lemma modeProduct_integrable {z : ℂ} (hz : z.re ≤ 1) {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ => modeProduct z p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi y))) := by
  refine (positive_kernel_integrable hy).mono' ?_ ?_
  · exact (show Continuous (fun p : ℝ × ℝ => modeProduct z p.1 p.2) by
      unfold modeProduct laplacePolynomial spectralExp; fun_prop).aestronglyMeasurable
  · apply (ae_prod_iff_ae_ae (by
      unfold modeProduct laplacePolynomial spectralExp
      measurability)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact modeProduct_bound hz hs.le (hy.trans hv).le

lemma resolventKernel_norm_bound {z : ℂ} (hz : z.re ≤ 1)
    (hγ : 10 ≤ |z.im|) {s y : ℝ} (hs : 0 ≤ s) (hy : 0 ≤ y) :
    ‖resolventKernel z s y‖ ≤ laplacePolynomial s * exp (-s * y) / 10 := by
  have he : ‖Complex.exp (-denominator z s * y)‖ ≤ exp (-s * y) := by
    rw [Complex.norm_exp]
    apply exp_le_exp.mpr
    simp only [denominator, Complex.mul_re, Complex.neg_re, Complex.sub_re,
      Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) hy]
  rw [resolventKernel, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (laplacePolynomial_nonneg hs)]
  calc
    _ ≤ (laplacePolynomial s / 10) * exp (-s * y) :=
      mul_le_mul (div_le_div_of_nonneg_left (laplacePolynomial_nonneg hs)
        (by norm_num) (denominator_norm hγ s)) he (norm_nonneg _)
        (div_nonneg (laplacePolynomial_nonneg hs) (by norm_num))
    _ = _ := by ring

lemma resolventMode_bound {z : ℂ} (hz : z.re ≤ 1)
    (hγ : 10 ≤ |z.im|) {y : ℝ} (hy : 0 < y) :
    ‖resolventMode z y‖ ≤ W y / 10 := by
  have h := norm_integral_le_of_norm_le ((laplace_weight_integrable hy).div_const 10)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact resolventKernel_norm_bound hz hγ hs.le hy.le)
  simpa only [resolventMode, integral_div, laplace_weight hy] using h

private lemma mode_v_integral {z : ℂ} (hz : z.re < 1) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    (∫ v : ℝ in Ioi y, modeProduct z s v) = resolventKernel z s y := by
  have hd : (-denominator z s).re < 0 := by
    simp only [denominator, Complex.neg_re, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.one_re]
    linarith
  have he : (fun v : ℝ => modeProduct z s v) =
      fun v : ℝ => (laplacePolynomial s : ℂ) * Complex.exp (-denominator z s * v) := by
    funext v
    dsimp [modeProduct, spectralExp]
    rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [denominator, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [he, integral_const_mul, integral_exp_mul_complex_Ioi hd y]
  dsimp [resolventKernel]
  simp only [div_neg, neg_div, neg_neg]
  ring

private lemma mode_s_integral {z : ℂ} {v : ℝ} (hv : 0 < v) :
    (∫ s : ℝ in Ioi 0, modeProduct z s v) = (W v : ℂ) * spectralExp z v := by
  dsimp only [modeProduct]
  rw [integral_mul_const]
  have he : (∫ s : ℝ in Ioi 0,
      (laplacePolynomial s : ℂ) * (exp (-s * v) : ℂ)) = (W v : ℂ) := by
    simp_rw [← Complex.ofReal_mul]
    calc
      _ = Complex.ofReal (∫ s : ℝ in Ioi 0, laplacePolynomial s * exp (-s * v)) :=
        integral_complex_ofReal
      _ = (W v : ℂ) := congrArg Complex.ofReal (laplace_weight hv)
  rw [he]

private lemma weighted_mode_integrable {z : ℂ} (hz : z.re ≤ 1) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => (W v : ℂ) * spectralExp z v) (Ioi y) := by
  refine (W_tail_integrable hy).mono' ?_ ?_
  · exact (show ContinuousOn (fun v : ℝ => (W v : ℂ) * spectralExp z v) (Ioi y) by
      intro v hv
      have hv0 := hy.trans hv
      dsimp [W, spectralExp]
      fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (W_nonneg (hy.trans hv).le)]
    exact mul_le_of_le_one_right (W_nonneg (hy.trans hv).le)
      (spectralExp_norm_le hz (hy.trans hv).le)

/-- Per-mode Fubini, with product integrability proved before exchange. -/
private theorem mode_resolvent_identity {z : ℂ} (hz : z.re < 1) {y : ℝ} (hy : 0 < y) :
    (∫ v : ℝ in Ioi y, (W v : ℂ) * spectralExp z v) = resolventMode z y := by
  calc
    _ = ∫ v : ℝ in Ioi y, ∫ s : ℝ in Ioi 0, modeProduct z s v := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (mode_s_integral (hy.trans hv)).symm
    _ = ∫ s : ℝ in Ioi 0, ∫ v : ℝ in Ioi y, modeProduct z s v :=
      (integral_integral_swap (modeProduct_integrable hz.le hy)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mode_v_integral hz hs y

lemma resolventMode_continuousOn {z : ℂ} (hz : z.re < 1) {H : ℝ} (hH : 0 < H) :
    ContinuousOn (resolventMode z) (Ici H) := by
  apply ((weighted_mode_integrable hz.le hH).continuousOn_Ici_primitive_Ioi).congr
  intro y hy
  exact (mode_resolvent_identity hz (hH.trans_le hy)).symm

private lemma spectralSeries_summable (S : CountableSpectrum) {v : ℝ} (hv : 0 ≤ v) :
    Summable (fun k : ℕ => S.coeff k * spectralExp (S.zero k) v) := by
  apply Summable.of_norm_bounded S.summable_norm
  intro k
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (spectralExp_norm_le (S.strip k).2.le hv)

/-- Complete countable exchange under the proved majorant ||c_k||*W(v). -/
theorem countable_resolvent_identity (S : CountableSpectrum) {y : ℝ} (hy : 0 < y) :
    spectralTail S y = ∑' k : ℕ, S.coeff k * resolventMode (S.zero k) y := by
  let f : ℕ → ℝ → ℂ := fun k v => S.coeff k * ((W v : ℂ) * spectralExp (S.zero k) v)
  have hmeas : ∀ k, AEStronglyMeasurable (f k) (volume.restrict (Ioi y)) := by
    intro k
    exact ((weighted_mode_integrable (S.strip k).2.le hy).const_mul _).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ v : ℝ ∂volume.restrict (Ioi y),
      ‖f k v‖ ≤ ‖S.coeff k‖ * W v := by
    intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    dsimp [f]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (W_nonneg (hy.trans hv).le)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right
      (W_nonneg (hy.trans hv).le) (spectralExp_norm_le (S.strip k).2.le (hy.trans hv).le))
      (norm_nonneg _)
  have hlim : ∀ᵐ v : ℝ ∂volume.restrict (Ioi y),
      HasSum (fun k => f k v) ((W v : ℂ) * spectralSeries S v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    convert (spectralSeries_summable S (hy.trans hv).le).hasSum.mul_left (W v : ℂ) using 1
    · funext k; dsimp [f]; ring
    · rfl
  have h := hasSum_integral_of_dominated_convergence
    (fun k v => ‖S.coeff k‖ * W v) hmeas hbound
    (ae_of_all _ (fun v => S.summable_norm.mul_right (W v)))
    (by simpa only [tsum_mul_right] using
      (W_tail_integrable hy).const_mul (∑' k : ℕ, ‖S.coeff k‖)) hlim
  change (∫ v : ℝ in Ioi y, (W v : ℂ) * spectralSeries S v) = _
  rw [← h.tsum_eq]
  congr 1
  funext k
  dsimp [f]
  rw [integral_const_mul, mode_resolvent_identity (S.strip k).2 hy]

lemma W_tail {y : ℝ} (hy : 0 < y) : (∫ v : ℝ in Ioi y, W v) = R y := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun v (hv : v ∈ Ici y) => R_hasDerivAt (hy.trans_le hv))
    (fun v (hv : v ∈ Ioi y) => neg_nonpos.mpr (W_nonneg (hy.trans hv).le))
    R_tendsto_zero
  rw [integral_neg, zero_sub] at h
  exact neg_injective h

private lemma spectralSeries_continuousOn (S : CountableSpectrum) :
    ContinuousOn (spectralSeries S) (Ici 0) := by
  apply continuousOn_tsum (fun k =>
    (show Continuous (fun v : ℝ => S.coeff k * spectralExp (S.zero k) v) by
      unfold spectralExp; fun_prop).continuousOn) S.summable_norm
  intro k v hv
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (spectralExp_norm_le (S.strip k).2.le hv)

private lemma spectralSeries_norm_le (S : CountableSpectrum) {v : ℝ} (hv : 0 ≤ v) :
    ‖spectralSeries S v‖ ≤ ∑' k : ℕ, ‖S.coeff k‖ := by
  refine (norm_tsum_le_tsum_norm (spectralSeries_summable S hv).norm).trans ?_
  apply ((spectralSeries_summable S hv).norm).tsum_le_tsum _ S.summable_norm
  intro k
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (spectralExp_norm_le (S.strip k).2.le hv)

lemma spectral_weighted_integrable (S : CountableSpectrum) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => (W v : ℂ) * spectralSeries S v) (Ioi y) := by
  refine ((W_tail_integrable hy).const_mul (∑' k : ℕ, ‖S.coeff k‖)).mono' ?_ ?_
  · exact (show ContinuousOn (fun v : ℝ => (W v : ℂ) * spectralSeries S v)
        (Ioi y) by
      apply ContinuousOn.mul
      · intro v hv
        have hv0 := hy.trans hv
        dsimp [W]; fun_prop (disch := positivity)
      · exact (spectralSeries_continuousOn S).mono (by intro v hv; exact (hy.trans hv).le)
      ).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (W_nonneg (hy.trans hv).le)]
    exact (mul_le_mul_of_nonneg_left (spectralSeries_norm_le S (hy.trans hv).le)
      (W_nonneg (hy.trans hv).le)).trans_eq (mul_comm _ _)

end D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
