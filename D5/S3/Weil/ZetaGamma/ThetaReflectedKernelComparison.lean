/- GID: D5/S3/Weil/ZetaGamma/ThetaReflectedKernelComparison
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ThetaReflectedKernelComparison
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: Complete physical theta entries strictly dominate their reflected entries. -/

import D5.S3.Analytic.Fourier.ThetaRadialCurvature
import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Strict reflection comparison for the complete physical theta kernel

The physical kernel is the literal formula (W2) in
`Library/Weil/suzuki2026screw.md`. Its radial changes of variable are (W13),
and the reflection comparison is the strict part of (W12).

The proof reuses the complete-kernel square-variable strict concavity from
`ThetaRadialCurvature` and the actual theta Gaussian bound. A symmetric-pair
comparison pays the strict product inequality, while monotonicity of cosh
preserves its direction. Both original weighted integrands and radial
integrands are genuinely integrable, and the change of variables retains
its Jacobian factor. The Gaussian estimate covers every fixed real weight
parameter, so the comparison holds for all nonnegative real parameters.
The conclusion compares individual physical entries with the full theta
series and infinite integration domain retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison

open Real Set MeasureTheory Filter
open scoped Topology NNReal
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Analytic.Fourier.ThetaRadialCurvature
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds

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

private def p (a b : ℝ) : ℝ := (a + b) / 2
private def d (a b : ℝ) : ℝ := |a - b| / 2
private def radialStart (a b : ℝ) : ℝ := (p a b) ^ 2 + (d a b) ^ 2
private def spread (c r : ℝ) : ℝ := 2 * c * sqrt (r - c ^ 2)
private def offsetProduct (c y : ℝ) : ℝ := romikPhi (y + c) * romikPhi (y - c)
private def radialProduct (c r : ℝ) : ℝ := offsetProduct c (sqrt (r - c ^ 2))
private def radialIntegrand (v c r : ℝ) : ℝ :=
  cosh (2 * v * sqrt (r - c ^ 2)) * radialProduct c r

/-- The literal complete physical kernel, with its signed shift. -/
def physicalKernel (v a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ y in Ioi |(a + b) / 2|,
    y * cosh (2 * v * y) *
      (romikPhi (y + (a - b) / 2) * romikPhi (y - (a - b) / 2))

/-- Strict concavity compares two symmetric pairs with the same center.
    Both inner points are strict convex combinations of the outer pair. -/
private theorem strictConcave_symmetric_sum {h : ℝ → ℝ}
    (hh : StrictConcaveOn ℝ (Ioi (0 : ℝ)) h)
    {r s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) :
    h (r - t) + h (r + t) < h (r - s) + h (r + s) := by
  have ht : 0 < t := hs.trans_lt hst
  have hden : 0 < 2 * t := by positivity
  let α := (t + s) / (2 * t)
  let β := (t - s) / (2 * t)
  have hα : 0 < α := div_pos (by linarith) hden
  have hβ : 0 < β := div_pos (sub_pos.mpr hst) hden
  have hab : α + β = 1 := by dsimp [α, β]; field_simp [ne_of_gt ht]; ring
  have hx : r - t ∈ Ioi (0 : ℝ) := sub_pos.mpr htr
  have hy : r + t ∈ Ioi (0 : ℝ) := by change 0 < r + t; linarith
  have hxy : r - t ≠ r + t := by linarith
  have hm : α * (r - t) + β * (r + t) = r - s := by
    dsimp [α, β]
    field_simp [ne_of_gt ht]
    ring
  have hp : β * (r - t) + α * (r + t) = r + s := by
    dsimp [α, β]
    field_simp [ne_of_gt ht]
    ring
  have h₁ := hh.2 hx hy hxy hα hβ hab
  have h₂ := hh.2 hx hy hxy hβ hα (by linarith : β + α = 1)
  simp only [smul_eq_mul, hm, hp] at h₁ h₂
  have hsum :
      (α * h (r - t) + β * h (r + t)) +
        (β * h (r - t) + α * h (r + t)) = h (r - t) + h (r + t) := by
    calc
      _ = (α + β) * h (r - t) + (α + β) * h (r + t) := by ring
      _ = _ := by rw [hab]; ring
  rw [← hsum]
  exact add_lt_add h₁ h₂

private theorem spread_geometry {c q r : ℝ}
    (hc : 0 ≤ c) (hcq : c < q) (hr : q ^ 2 + c ^ 2 < r)
    (hne : r ≠ 2 * q ^ 2) :
    0 ≤ spread c r ∧ spread c r < spread q r ∧ spread q r < r := by
  have hq : 0 < q := hc.trans_lt hcq
  have hrc : 0 < r - c ^ 2 := by nlinarith [sq_nonneg q]
  have hrq : 0 < r - q ^ 2 := by nlinarith [sq_nonneg c]
  have hr0 : 0 < r := by nlinarith [sq_nonneg q, sq_nonneg c]
  have hkc : 0 ≤ spread c r := by dsimp [spread]; positivity
  have hkq : 0 < spread q r := by
    dsimp [spread]
    exact mul_pos (mul_pos (by norm_num) hq) (sqrt_pos.mpr hrq)
  have hsqc : (spread c r) ^ 2 = 4 * c ^ 2 * (r - c ^ 2) := by
    simp only [spread, mul_pow, sq_sqrt hrc.le]
    ring
  have hsqq : (spread q r) ^ 2 = 4 * q ^ 2 * (r - q ^ 2) := by
    simp only [spread, mul_pow, sq_sqrt hrq.le]
    ring
  have hbase : 0 < q ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hcq) (by linarith : 0 < q + c)]
  have hdiff : 0 < (spread q r) ^ 2 - (spread c r) ^ 2 := by
    have heq : (spread q r) ^ 2 - (spread c r) ^ 2 =
        4 * (q ^ 2 - c ^ 2) * (r - (q ^ 2 + c ^ 2)) := by
      rw [hsqq, hsqc]
      ring
    rw [heq]
    exact mul_pos (mul_pos (by norm_num) hbase) (sub_pos.mpr hr)
  have hkcq : spread c r < spread q r := by
    by_contra h
    have hle : spread q r ≤ spread c r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hkc hkq.le)]
  have hedge : 0 < r ^ 2 - (spread q r) ^ 2 := by
    have heq : r ^ 2 - (spread q r) ^ 2 = (r - 2 * q ^ 2) ^ 2 := by
      rw [hsqq]
      ring
    rw [heq]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hkqr : spread q r < r := by
    by_contra h
    have hle : r ≤ spread q r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hkq.le hr0.le)]
  exact ⟨hkc, hkcq, hkqr⟩

private theorem log_square_pair (c r : ℝ) (hr : c ^ 2 < r) :
    log (romikPhi (sqrt (r - spread c r))) +
        log (romikPhi (sqrt (r + spread c r))) =
      log (romikPhi (sqrt (r - c ^ 2) - c)) +
        log (romikPhi (sqrt (r - c ^ 2) + c)) := by
  have hs := sq_sqrt (sub_pos.mpr hr).le
  have hm : r - spread c r = (sqrt (r - c ^ 2) - c) ^ 2 := by
    dsimp [spread]
    nlinarith [hs]
  have hp : r + spread c r = (sqrt (r - c ^ 2) + c) ^ 2 := by
    dsimp [spread]
    nlinarith [hs]
  rw [hm, hp, sqrt_sq_eq_abs, phi_abs, sqrt_sq_eq_abs, phi_abs]

/-- The full actual theta products compare strictly on the common radial ray.
    The excluded singleton is the only point where an outer square is zero. -/
private theorem radialProduct_lt {c q r : ℝ}
    (hc : 0 ≤ c) (hcq : c < q) (hr : q ^ 2 + c ^ 2 < r)
    (hne : r ≠ 2 * q ^ 2) : radialProduct q r < radialProduct c r := by
  have hg := spread_geometry hc hcq hr hne
  have hlog := strictConcave_symmetric_sum
    actual_phi_radial_curvature_and_square_concavity.2 hg.1 hg.2.1 hg.2.2
  have hrc : c ^ 2 < r := by nlinarith [sq_nonneg q]
  have hrq : q ^ 2 < r := by nlinarith [sq_nonneg c]
  rw [log_square_pair q r hrq, log_square_pair c r hrc] at hlog
  have he := exp_lt_exp.mpr hlog
  simp only [exp_add,
    exp_log (phi_pos (sqrt (r - q ^ 2) - q)),
    exp_log (phi_pos (sqrt (r - q ^ 2) + q)),
    exp_log (phi_pos (sqrt (r - c ^ 2) - c)),
    exp_log (phi_pos (sqrt (r - c ^ 2) + c))] at he
  simpa only [radialProduct, offsetProduct, mul_comm] using he

private theorem radialIntegrand_pos (v c r : ℝ) : 0 < radialIntegrand v c r :=
  mul_pos (cosh_pos _) (mul_pos (phi_pos _) (phi_pos _))

/-- The cosh weight preserves the strict actual-product comparison, including v=0. -/
private theorem radialIntegrand_lt {v c q r : ℝ} (hv : 0 ≤ v)
    (hc : 0 ≤ c) (hcq : c < q) (hr : q ^ 2 + c ^ 2 < r)
    (hne : r ≠ 2 * q ^ 2) : radialIntegrand v q r < radialIntegrand v c r := by
  have hq : 0 < q := hc.trans_lt hcq
  have hsq : c ^ 2 ≤ q ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcq.le) (by linarith : 0 ≤ q + c)]
  have hcosh : cosh (2 * v * sqrt (r - q ^ 2)) ≤
      cosh (2 * v * sqrt (r - c ^ 2)) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by linarith)) (by positivity)
  calc
    _ < cosh (2 * v * sqrt (r - q ^ 2)) * radialProduct c r :=
      mul_lt_mul_of_pos_left (radialProduct_lt hc hcq hr hne) (cosh_pos _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcosh (mul_pos (phi_pos _) (phi_pos _)).le

private theorem pd_geometry {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ d a b ∧ d a b < p a b := by
  have hab : |a - b| < a + b := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact ⟨div_nonneg (abs_nonneg _) (by norm_num),
    div_lt_div_of_pos_right hab (by norm_num)⟩

private theorem actual_reflected_integrand_lt {a b v r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hr : radialStart a b < r) (hne : r ≠ 2 * (p a b) ^ 2) :
    radialIntegrand v (p a b) r < radialIntegrand v (d a b) r := by
  have hpd := pd_geometry ha hb
  exact radialIntegrand_lt hv hpd.1 hpd.2 hr hne

private theorem cosh_gaussian_bound (v y : ℝ) :
    cosh (2 * v * y) ≤ exp (y ^ 2 + v ^ 2) := by
  have hplus : exp (2 * v * y) ≤ exp (y ^ 2 + v ^ 2) :=
    exp_le_exp.mpr (by nlinarith [sq_nonneg (y - v)])
  have hminus : exp (-(2 * v * y)) ≤ exp (y ^ 2 + v ^ 2) :=
    exp_le_exp.mpr (by nlinarith [sq_nonneg (y + v)])
  rw [cosh_eq]
  linarith

private theorem exp_weight_cancel (v t : ℝ) :
    exp (t + v ^ 2) * (M ^ 2 * exp ((-2 : ℝ) * t)) =
      M ^ 2 * exp (v ^ 2) * exp (-t) := by
  calc
    _ = M ^ 2 * (exp (t + v ^ 2) * exp ((-2 : ℝ) * t)) := by ring
    _ = M ^ 2 * exp ((t + v ^ 2) + (-2 : ℝ) * t) := by rw [← exp_add]
    _ = _ := by
      rw [show (t + v ^ 2) + (-2 : ℝ) * t = v ^ 2 + -t by ring, exp_add]
      ring

/-- Gaussian decay absorbs every fixed real cosh parameter. -/
private theorem radialIntegrand_gaussian_bound (v c : ℝ) {r : ℝ} (hr : c ^ 2 ≤ r) :
    ‖radialIntegrand v c r‖ ≤ M ^ 2 * exp (v ^ 2) * exp (-r) := by
  have hs := sq_sqrt (sub_nonneg.mpr hr)
  have hp := phi_product_gaussian (sqrt (r - c ^ 2) + c) (sqrt (r - c ^ 2) - c)
  have heq : -((sqrt (r - c ^ 2) + c) ^ 2 +
      (sqrt (r - c ^ 2) - c) ^ 2) = (-2 : ℝ) * r := by nlinarith [hs]
  have hp' : radialProduct c r ≤ M ^ 2 * exp ((-2 : ℝ) * r) := by
    simpa only [radialProduct, offsetProduct, heq,
      abs_of_pos (mul_pos (phi_pos _) (phi_pos _))] using hp
  have hcosh : cosh (2 * v * sqrt (r - c ^ 2)) ≤ exp (r + v ^ 2) := by
    have hc := cosh_gaussian_bound v (sqrt (r - c ^ 2))
    rw [hs] at hc
    exact hc.trans (exp_le_exp.mpr (by nlinarith [sq_nonneg c]))
  rw [Real.norm_eq_abs, abs_of_pos (radialIntegrand_pos v c r)]
  calc
    _ ≤ exp (r + v ^ 2) * (M ^ 2 * exp ((-2 : ℝ) * r)) :=
      mul_le_mul hcosh hp' (mul_pos (phi_pos _) (phi_pos _)).le (exp_nonneg _)
    _ = _ := exp_weight_cancel v r

private theorem radialIntegrand_continuous (v c : ℝ) :
    Continuous (radialIntegrand v c) := by
  have hs : Continuous (fun r : ℝ => sqrt (r - c ^ 2)) := by fun_prop
  exact (continuous_cosh.comp (continuous_const.mul hs)).mul
    ((phi_continuous.comp (hs.add_const c)).mul
      (phi_continuous.comp (hs.sub continuous_const)))

private theorem radialIntegrand_integrable (v c b : ℝ) :
    IntegrableOn (radialIntegrand v c) (Ioi (b ^ 2 + c ^ 2)) := by
  have hm := (integrableOn_exp_mul_Ioi
    (show (-1 : ℝ) < 0 by norm_num) (b ^ 2 + c ^ 2)).const_mul
      (M ^ 2 * exp (v ^ 2))
  apply hm.mono' (radialIntegrand_continuous v c).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : b ^ 2 + c ^ 2 < r := hr
  simpa only [neg_one_mul] using
    radialIntegrand_gaussian_bound v c (by nlinarith [sq_nonneg b] : c ^ 2 ≤ r)

/-- The literal weighted y-integrands are genuinely L1 on the entire real line. -/
private theorem physical_integrand_integrable (v c : ℝ) :
    Integrable (fun y : ℝ => y * cosh (2 * v * y) * offsetProduct c y) := by
  have hm := ((integrable_mul_exp_neg_mul_sq
    (show (0 : ℝ) < 1 by norm_num)).norm).const_mul (M ^ 2 * exp (v ^ 2))
  have hc : Continuous (fun y : ℝ => y * cosh (2 * v * y) * offsetProduct c y) :=
    (continuous_id.mul (continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      ((phi_continuous.comp (continuous_id.add_const c)).mul
        (phi_continuous.comp (continuous_id.sub continuous_const)))
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  have hp : |offsetProduct c y| ≤ M ^ 2 * exp ((-2 : ℝ) * y ^ 2) := by
    have h := phi_product_gaussian (y + c) (y - c)
    exact h.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by nlinarith [sq_nonneg c])) (sq_nonneg M))
  calc
    _ = |y| * cosh (2 * v * y) * |offsetProduct c y| := by
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (cosh_pos _)]
    _ ≤ (|y| * exp (y ^ 2 + v ^ 2)) * (M ^ 2 * exp ((-2 : ℝ) * y ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (cosh_gaussian_bound v y) (abs_nonneg _))
        hp (abs_nonneg _) (mul_nonneg (abs_nonneg _) (exp_nonneg _))
    _ = |y| * (M ^ 2 * exp (v ^ 2) * exp (-(y ^ 2))) := by
      rw [mul_assoc, exp_weight_cancel v (y ^ 2)]
    _ = M ^ 2 * exp (v ^ 2) * ‖y * exp (-(1 : ℝ) * y ^ 2)‖ := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      simp only [neg_one_mul]
      ring

private theorem offsetProduct_abs (c y : ℝ) : offsetProduct |c| y = offsetProduct c y := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
  · rw [abs_of_neg (lt_of_not_ge hc)]
    simp only [offsetProduct]
    rw [show y + -c = y - c by ring,
      show y - -c = y + c by ring,
      mul_comm]

private theorem abs_half_difference (a b : ℝ) : |(a - b) / 2| = d a b := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rfl

private theorem physicalKernel_positive_offset (v a b : ℝ) :
    physicalKernel v a b = (1 / 2 : ℝ) *
      ∫ y in Ioi |p a b|, y * cosh (2 * v * y) * offsetProduct (d a b) y := by
  unfold physicalKernel
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  change y * cosh (2 * v * y) * offsetProduct ((a - b) / 2) y =
    y * cosh (2 * v * y) * offsetProduct (d a b) y
  rw [← offsetProduct_abs ((a - b) / 2) y, abs_half_difference]

/-- The complete one-dimensional substitution, including dr=2*y*dy. -/
private theorem radial_integral_identity (v c b : ℝ) (hb : 0 ≤ b) :
    (1 / 2 : ℝ) * (∫ y in Ioi b, y * cosh (2 * v * y) * offsetProduct c y) =
      (1 / 4 : ℝ) * ∫ r in Ioi (b ^ 2 + c ^ 2), radialIntegrand v c r := by
  have h := square_shift_substitution (radialIntegrand v c) (b := b) (c := c ^ 2) hb
  have heq : (∫ y in Ioi b, y * radialIntegrand v c (y ^ 2 + c ^ 2)) =
      ∫ y in Ioi b, y * cosh (2 * v * y) * offsetProduct c y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hyb : b < y := hy
    have hy0 : 0 ≤ y := hb.trans hyb.le
    dsimp only [radialIntegrand, radialProduct]
    rw [add_sub_cancel_right, sqrt_sq hy0]
    ring
  rw [heq] at h
  linarith

private theorem physicalKernel_radial_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    physicalKernel v a b = (1 / 4 : ℝ) *
      ∫ r in Ioi (radialStart a b), radialIntegrand v (d a b) r := by
  have hp : 0 < p a b := by dsimp [p]; positivity
  rw [physicalKernel_positive_offset, abs_of_pos hp]
  exact radial_integral_identity v (d a b) (p a b) hp.le

private theorem physicalKernel_reflected_radial_identity {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    physicalKernel v a (-b) = (1 / 4 : ℝ) *
      ∫ r in Ioi (radialStart a b), radialIntegrand v (p a b) r := by
  have hd : 0 ≤ d a b := (pd_geometry ha hb).1
  have heq : physicalKernel v a (-b) = (1 / 2 : ℝ) *
      ∫ y in Ioi (d a b), y * cosh (2 * v * y) * offsetProduct (p a b) y := by
    unfold physicalKernel
    have hlow : |(a + -b) / 2| = d a b := by
      rw [show a + -b = a - b by ring, abs_half_difference]
    rw [hlow]
    simp only [sub_neg_eq_add, p, offsetProduct]
  rw [heq, radial_integral_identity v (p a b) (d a b) hd]
  simp only [radialStart, add_comm]

private theorem positive_physical_integral (v c b : ℝ) (hb : 0 ≤ b) :
    0 < ∫ y in Ioi b, y * cosh (2 * v * y) * offsetProduct c y := by
  let f : ℝ → ℝ := fun y => y * cosh (2 * v * y) * offsetProduct c y
  have hpos (y : ℝ) (hy : y ∈ Ioi b) : 0 < f y := by
    have hyb : b < y := hy
    exact mul_pos (mul_pos (lt_of_le_of_lt hb hyb) (cosh_pos _))
      (mul_pos (phi_pos _) (phi_pos _))
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi b)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hpos y hy).le
  have hsub : Ioo b (b + 1) ⊆ Function.support f ∩ Ioi b := by
    intro y hy
    exact ⟨ne_of_gt (hpos y hy.1), hy.1⟩
  have hμ : 0 < volume (Ioo b (b + 1)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hnn
    (physical_integrand_integrable v c).integrableOn).mpr
      (hμ.trans_le (measure_mono hsub))

/-- The complete reflected entries compare strictly for every finite v>=0.
    This assertion concerns individual entries, with no matrix-positivity claim. -/
theorem physical_kernel_reflection_comparison {a b v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v) :
    0 < physicalKernel v a (-b) ∧ physicalKernel v a (-b) < physicalKernel v a b := by
  have hpd := pd_geometry ha hb
  have hphysical : 0 < physicalKernel v a (-b) := by
    have hp := positive_physical_integral v (p a b) (d a b) hpd.1
    unfold physicalKernel
    have hlow : |(a + -b) / 2| = d a b := by
      rw [show a + -b = a - b by ring, abs_half_difference]
    rw [hlow]
    simpa only [sub_neg_eq_add, p, offsetProduct] using
      (mul_pos (show (0 : ℝ) < 1 / 2 by norm_num) hp)
  have hid : IntegrableOn (radialIntegrand v (d a b)) (Ioi (radialStart a b)) :=
    radialIntegrand_integrable v (d a b) (p a b)
  have hip : IntegrableOn (radialIntegrand v (p a b)) (Ioi (radialStart a b)) := by
    simpa only [radialStart, add_comm] using radialIntegrand_integrable v (p a b) (d a b)
  let Δ : ℝ → ℝ := fun r => radialIntegrand v (d a b) r - radialIntegrand v (p a b) r
  have hΔint : IntegrableOn Δ (Ioi (radialStart a b)) := hid.sub hip
  have hΔnn : 0 ≤ᵐ[volume.restrict (Ioi (radialStart a b))] Δ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne (2 * (p a b) ^ 2))] with r hr hne
    exact (sub_pos.mpr (actual_reflected_integrand_lt ha hb hv hr hne)).le
  have hsub : Ioo (radialStart a b) (2 * (p a b) ^ 2) ⊆
      Function.support Δ ∩ Ioi (radialStart a b) := by
    intro r hr
    exact ⟨ne_of_gt (sub_pos.mpr
      (actual_reflected_integrand_lt ha hb hv hr.1 (ne_of_lt hr.2))), hr.1⟩
  have hwidth : radialStart a b < 2 * (p a b) ^ 2 := by
    dsimp only [radialStart]
    nlinarith [mul_pos (sub_pos.mpr hpd.2)
      (by linarith [hpd.1] : 0 < p a b + d a b)]
  have hμ : 0 < volume (Ioo (radialStart a b) (2 * (p a b) ^ 2)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hwidth)
  have hΔpos : 0 < ∫ r in Ioi (radialStart a b), Δ r :=
    (setIntegral_pos_iff_support_of_nonneg_ae hΔnn hΔint).mpr
      (hμ.trans_le (measure_mono hsub))
  change 0 < ∫ r in Ioi (radialStart a b),
    radialIntegrand v (d a b) r - radialIntegrand v (p a b) r at hΔpos
  rw [integral_sub hid hip] at hΔpos
  refine ⟨hphysical, ?_⟩
  rw [physicalKernel_reflected_radial_identity ha hb, physicalKernel_radial_identity ha hb]
  linarith


end D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison
