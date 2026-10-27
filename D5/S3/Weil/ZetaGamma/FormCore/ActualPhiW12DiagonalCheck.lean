import D5.S3.Analytic.Fourier.ThetaRadialCurvature
import D5.S3.Weil.ZetaGamma.FormCore.EvenCuspConvolutionC2Check
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
noncomputable section
/- Actual diagonal consumer. Add to the import block:
     import D5.S3.Analytic.Fourier.ThetaRadialCurvature
     import Mathlib.MeasureTheory.Function.JacobianOneDim
     import Mathlib.MeasureTheory.Integral.Bochner.Set
     import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
   The diagonal is Suzuki's literal L0(a,a), from K0 in (W2)/(W49).
   This fragment makes no assertion for the full off-diagonal kernel. -/

namespace RhTransient.ActualPhiW12Diagonal

open Real Set MeasureTheory Filter
open scoped Topology NNReal
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Analytic.Fourier.ThetaRadialCurvature

def front (r : ℝ) : ℝ := (romikPhi (sqrt r)) ^ 2
def shiftedProduct (a r : ℝ) : ℝ :=
  romikPhi (sqrt (r - a ^ 2) + a) * romikPhi (sqrt (r - a ^ 2) - a)
def radialDefect (a r : ℝ) : ℝ := front r - shiftedProduct a r

/-- The actual diagonal L0(a,a), with both original weighted integrals. -/
def diagonalL0 (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ y in Ioi a, y * (romikPhi y) ^ 2) -
    (1 / 2 : ℝ) * (∫ y in Ioi 0, y * (romikPhi (y + a) * romikPhi (y - a)))

private theorem phi_pos (x : ℝ) : 0 < romikPhi x := by
  rw [romikPhi_eq_source]
  exact (source_theta_gaussian_bound x).1

private theorem phi_continuous : Continuous romikPhi := by
  have heq : romikPhi = sourceThetaKernel := funext romikPhi_eq_source
  rw [heq]
  exact source_theta_continuous

private theorem phi_abs (x : ℝ) : romikPhi |x| = romikPhi x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    exact romikPhi_even x

/-- Strict midpoint concavity in the square variable gives the literal
    product inequality. Only r=2*a^2 is excluded because one square is zero,
    outside the open domain of the supplied strict-concavity theorem. -/
theorem radialDefect_pos {a r : ℝ} (ha : 0 < a) (hr : a ^ 2 < r)
    (hne : r ≠ 2 * a ^ 2) : 0 < radialDefect a r := by
  let t := sqrt (r - a ^ 2)
  have ht : 0 < t := sqrt_pos.mpr (sub_pos.mpr hr)
  have htsq : t ^ 2 = r - a ^ 2 := sq_sqrt (sub_pos.mpr hr).le
  have htne : t ≠ a := by
    intro heq
    apply hne
    rw [heq] at htsq
    linarith
  have hu : 0 < (t + a) ^ 2 := sq_pos_of_pos (add_pos ht ha)
  have hv : 0 < (t - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr htne)
  have huv : (t + a) ^ 2 ≠ (t - a) ^ 2 := by
    intro heq
    nlinarith [mul_pos ht ha]
  have hmid : (1 / 2 : ℝ) * (t + a) ^ 2 + (1 / 2 : ℝ) * (t - a) ^ 2 = r := by
    nlinarith [htsq]
  have hconc := actual_phi_radial_curvature_and_square_concavity.2
  have h := hconc.2 hu hv huv
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  rw [hmid, sqrt_sq_eq_abs, abs_of_pos (add_pos ht ha), sqrt_sq_eq_abs, phi_abs] at h
  have hlog : log (romikPhi (t + a)) + log (romikPhi (t - a)) <
      2 * log (romikPhi (sqrt r)) := by linarith
  have hexp := exp_lt_exp.mpr hlog
  rw [show 2 * log (romikPhi (sqrt r)) =
      log (romikPhi (sqrt r)) + log (romikPhi (sqrt r)) by ring] at hexp
  simp only [exp_add, exp_log (phi_pos (t + a)), exp_log (phi_pos (t - a)),
    exp_log (phi_pos (sqrt r))] at hexp
  change 0 < (romikPhi (sqrt r)) ^ 2 -
    romikPhi (t + a) * romikPhi (t - a)
  nlinarith

private def M : ℝ := ∑' n : ℕ, thetaMajorant n

private theorem M_nonneg : 0 ≤ M :=
  tsum_nonneg (fun n => by dsimp [thetaMajorant]; positivity)

private theorem phi_product_gaussian (u v : ℝ) :
    |romikPhi u * romikPhi v| ≤ M ^ 2 * exp (-(u ^ 2 + v ^ 2)) := by
  have hu := (source_theta_gaussian_bound u).2
  have hv := (source_theta_gaussian_bound v).2
  rw [← romikPhi_eq_source u] at hu
  rw [← romikPhi_eq_source v] at hv
  change romikPhi u ≤ M * exp (-u ^ 2) at hu
  change romikPhi v ≤ M * exp (-v ^ 2) at hv
  rw [abs_of_pos (mul_pos (phi_pos u) (phi_pos v))]
  calc
    _ ≤ (M * exp (-u ^ 2)) * (M * exp (-v ^ 2)) :=
      mul_le_mul hu hv (phi_pos v).le (mul_nonneg M_nonneg (exp_nonneg _))
    _ = _ := by rw [show -(u ^ 2 + v ^ 2) = -u ^ 2 + -v ^ 2 by ring, exp_add]; ring

private theorem front_bound {a r : ℝ} (hr : a ^ 2 < r) :
    |front r| ≤ M ^ 2 * exp ((-2 : ℝ) * r) := by
  have hr0 : 0 ≤ r := (sq_nonneg a).trans hr.le
  have h := phi_product_gaussian (sqrt r) (sqrt r)
  simpa only [front, ← pow_two, sq_sqrt hr0,
    show -(r + r) = (-2 : ℝ) * r by ring] using h

private theorem shiftedProduct_bound {a r : ℝ} (hr : a ^ 2 < r) :
    |shiftedProduct a r| ≤ M ^ 2 * exp ((-2 : ℝ) * r) := by
  have hs := sq_sqrt (sub_pos.mpr hr).le
  have h := phi_product_gaussian (sqrt (r - a ^ 2) + a) (sqrt (r - a ^ 2) - a)
  have heq : -((sqrt (r - a ^ 2) + a) ^ 2 +
      (sqrt (r - a ^ 2) - a) ^ 2) = (-2 : ℝ) * r := by nlinarith [hs]
  simpa only [shiftedProduct, heq] using h

theorem radialDefect_gaussian_bound {a r : ℝ} (hr : a ^ 2 < r) :
    |radialDefect a r| ≤ 2 * M ^ 2 * exp ((-2 : ℝ) * r) := by
  calc
    _ ≤ |front r| + |shiftedProduct a r| := by
      simpa only [radialDefect, Real.norm_eq_abs] using
        norm_sub_le (front r) (shiftedProduct a r)
    _ ≤ M ^ 2 * exp ((-2 : ℝ) * r) + M ^ 2 * exp ((-2 : ℝ) * r) :=
      add_le_add (front_bound hr) (shiftedProduct_bound hr)
    _ = _ := by ring

private theorem front_integrable (a : ℝ) : IntegrableOn front (Ioi (a ^ 2)) := by
  have hm := (integrableOn_exp_mul_Ioi
    (show (-2 : ℝ) < 0 by norm_num) (a ^ 2)).const_mul (M ^ 2)
  have hc : Continuous front := (phi_continuous.comp continuous_sqrt).pow 2
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simpa only [Real.norm_eq_abs] using front_bound hr

private theorem shiftedProduct_integrable (a : ℝ) :
    IntegrableOn (shiftedProduct a) (Ioi (a ^ 2)) := by
  have hm := (integrableOn_exp_mul_Ioi
    (show (-2 : ℝ) < 0 by norm_num) (a ^ 2)).const_mul (M ^ 2)
  have hs : Continuous (fun r : ℝ => sqrt (r - a ^ 2)) := by fun_prop
  have hc : Continuous (shiftedProduct a) :=
    (phi_continuous.comp (hs.add_const a)).mul
      (phi_continuous.comp (hs.sub continuous_const))
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simpa only [Real.norm_eq_abs] using shiftedProduct_bound hr

theorem radialDefect_integrable (a : ℝ) :
    IntegrableOn (radialDefect a) (Ioi (a ^ 2)) :=
  (front_integrable a).sub (shiftedProduct_integrable a)

/-- The original weighted integrands also satisfy genuine full-line L1,
    directly from the same Gaussian bound. No integral-undef convention is used. -/
private theorem weighted_shift_integrable (a : ℝ) :
    Integrable (fun y : ℝ => y * (romikPhi (y + a) * romikPhi (y - a))) := by
  have hm := ((integrable_mul_exp_neg_mul_sq
    (show (0 : ℝ) < 2 by norm_num)).norm).const_mul (M ^ 2)
  have hc : Continuous (fun y : ℝ => y * (romikPhi (y + a) * romikPhi (y - a))) :=
    continuous_id.mul ((phi_continuous.comp (continuous_id.add_const a)).mul
      (phi_continuous.comp (continuous_id.sub continuous_const)))
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  have hp := phi_product_gaussian (y + a) (y - a)
  have he : exp (-((y + a) ^ 2 + (y - a) ^ 2)) ≤ exp (-(2 : ℝ) * y ^ 2) :=
    exp_le_exp.mpr (by nlinarith [sq_nonneg a])
  calc
    _ = |y| * |romikPhi (y + a) * romikPhi (y - a)| := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |y| * (M ^ 2 * exp (-((y + a) ^ 2 + (y - a) ^ 2))) :=
      mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ ≤ |y| * (M ^ 2 * exp (-(2 : ℝ) * y ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (sq_nonneg M)) (abs_nonneg _)
    _ = M ^ 2 * ‖y * exp (-(2 : ℝ) * y ^ 2)‖ := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      ring

theorem diagonalL0_original_integrable (a : ℝ) :
    IntegrableOn (fun y : ℝ => y * (romikPhi y) ^ 2) (Ioi a) ∧
      IntegrableOn (fun y : ℝ => y * (romikPhi (y + a) * romikPhi (y - a))) (Ioi 0) := by
  refine ⟨?_, (weighted_shift_integrable a).integrableOn⟩
  simpa only [add_zero, sub_zero, pow_two] using
    (weighted_shift_integrable 0).integrableOn (s := Ioi a)

/-- Complete injective change of variables, retaining the factor dr=2*y*dy.
    The Jacobian theorem also applies to the totalized Bochner integrals;
    the actual consumers below separately pay both radial L1 conditions. -/
private theorem square_shift_substitution (H : ℝ → ℝ) {b c : ℝ} (hb : 0 ≤ b) :
    (∫ r in Ioi (b ^ 2 + c), H r) =
      2 * (∫ y in Ioi b, y * H (y ^ 2 + c)) := by
  have himage : (fun y : ℝ => y ^ 2 + c) '' Ioi b = Ioi (b ^ 2 + c) := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyb : b < y := hy
      have hy0 : 0 ≤ y := hb.trans hyb.le
      have hprod := mul_pos (sub_pos.mpr hyb) (by linarith : 0 < y + b)
      change b ^ 2 + c < y ^ 2 + c
      nlinarith
    · intro hr
      have hr0 : b ^ 2 + c < r := hr
      have hrc : 0 ≤ r - c := by nlinarith [sq_nonneg b]
      have hs := sq_sqrt hrc
      have ht : b < sqrt (r - c) := by
        have h := sqrt_lt_sqrt (sq_nonneg b) (show b ^ 2 < r - c by linarith)
        simpa only [sqrt_sq hb] using h
      exact ⟨sqrt (r - c), ht, by linarith⟩
  have hinj : InjOn (fun y : ℝ => y ^ 2 + c) (Ioi b) := by
    intro y hy z hz heq
    have hyb : b < y := hy
    have hzb : b < z := hz
    have hy0 : 0 ≤ y := hb.trans hyb.le
    have hz0 : 0 ≤ z := hb.trans hzb.le
    have hsq : y ^ 2 = z ^ 2 := by linarith
    have h := congrArg sqrt hsq
    simpa only [sqrt_sq hy0, sqrt_sq hz0] using h
  have hder (y : ℝ) (_hy : y ∈ Ioi b) :
      HasDerivWithinAt (fun t : ℝ => t ^ 2 + c) (2 * y) (Ioi b) y := by
    simpa only [Pi.pow_apply, id_eq, show (2 : ℕ) - 1 = 1 by rfl,
      pow_one, mul_one, Nat.cast_ofNat] using!
      (((hasDerivAt_id y).pow 2).add_const c).hasDerivWithinAt (s := Ioi b)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj H
  rw [himage] at h
  calc
    _ = ∫ y in Ioi b, |2 * y| * H (y ^ 2 + c) := by
      simpa only [smul_eq_mul] using h
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hyb : b < y := hy
      change |2 * y| * H (y ^ 2 + c) = 2 * (y * H (y ^ 2 + c))
      rw [abs_of_nonneg (by linarith : 0 ≤ 2 * y)]
      ring

/-- Exact diagonal identity, from both original y-integrals to one radial
    difference. The two radial summands are genuinely integrable. -/
theorem diagonalL0_radial_identity {a : ℝ} (ha : 0 < a) :
    diagonalL0 a = (1 / 4 : ℝ) * ∫ r in Ioi (a ^ 2), radialDefect a r := by
  have hfront := square_shift_substitution front (b := a) (c := 0) ha.le
  have hshift := square_shift_substitution (shiftedProduct a) (b := 0) (c := a ^ 2)
    (by norm_num : (0 : ℝ) ≤ 0)
  simp only [add_zero] at hfront
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at hshift
  have heq1 : (∫ y in Ioi a, y * front (y ^ 2)) =
      ∫ y in Ioi a, y * (romikPhi y) ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hay : a < y := hy
    dsimp only [front]
    rw [sqrt_sq (by linarith : 0 ≤ y)]
  have heq2 : (∫ y in Ioi 0, y * shiftedProduct a (y ^ 2 + a ^ 2)) =
      ∫ y in Ioi 0, y * (romikPhi (y + a) * romikPhi (y - a)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    dsimp only [shiftedProduct]
    rw [add_sub_cancel_right, sqrt_sq hy0.le]
  rw [heq1] at hfront
  rw [heq2] at hshift
  change diagonalL0 a = (1 / 4 : ℝ) *
    ∫ r in Ioi (a ^ 2), front r - shiftedProduct a r
  rw [integral_sub (front_integrable a) (shiftedProduct_integrable a)]
  dsimp only [diagonalL0]
  linarith

/-- Strict positivity is obtained on a positive-measure interval, while the
    exceptional point 2*a^2 is removed from the whole ray only a.e. -/
theorem diagonalL0_pos {a : ℝ} (ha : 0 < a) : 0 < diagonalL0 a := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (a ^ 2))] radialDefect a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne (2 * a ^ 2))] with r hr hne
    exact (radialDefect_pos ha hr hne).le
  have hsubset : Ioo (a ^ 2) (2 * a ^ 2) ⊆
      Function.support (radialDefect a) ∩ Ioi (a ^ 2) := by
    intro r hr
    exact ⟨ne_of_gt (radialDefect_pos ha hr.1 (ne_of_lt hr.2)), hr.1⟩
  have hμ : 0 < volume (Ioo (a ^ 2) (2 * a ^ 2)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by nlinarith [sq_pos_of_pos ha])
  have hpos : 0 < ∫ r in Ioi (a ^ 2), radialDefect a r :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnn (radialDefect_integrable a)).mpr
      (hμ.trans_le (measure_mono hsubset))
  rw [diagonalL0_radial_identity ha]
  exact mul_pos (by norm_num) hpos

end RhTransient.ActualPhiW12Diagonal

#print axioms RhTransient.ActualPhiW12Diagonal.diagonalL0_pos
#print axioms RhTransient.ActualGaussianCuspSupplier.suzukiGaussianAutocorrelation_C2
#print axioms D5.S3.Analytic.Fourier.ThetaRadialCurvature.actual_phi_radial_curvature_and_square_concavity
