/- GID: D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/GaussianCoshKernel
   mirror-E: none(waiver:symbolic-uniform-integral-estimate)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Series, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: A compact-uniform Gaussian-cosh local integral expansion with an exact real-power remainder. -/

import D5.S3.TotalVariation.Asymptotics.StatLeanFourierSuppliers
import D5.S3.Zeros.Jensen.FactorialJensenKernelBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open StatLean.HypothesisTesting

namespace D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel

/-- The actual positive-part integral against the standard normal density. -/
def gaussianCoshIntegral (q d : ℝ) : ℝ :=
  ∫ u : ℝ, stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0

private theorem density_bounds (u : ℝ) :
    0 ≤ stdNormalPDF u ∧ stdNormalPDF u ≤ stdNormalPDF 0 ∧
      |stdNormalPDF u - stdNormalPDF 0| ≤ stdNormalPDF 0 * (u ^ 2 / 2) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have he : Real.exp (-u ^ 2 / 2) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -u ^ 2 / 2 ≤ 0 by nlinarith [sq_nonneg u])
  have hl := Real.add_one_le_exp (-u ^ 2 / 2)
  have h0 : stdNormalPDF 0 = 1 / Real.sqrt (2 * Real.pi) := by
    simp [stdNormalPDF]
  have hu : stdNormalPDF u ≤ stdNormalPDF 0 := by
    rw [stdNormalPDF, h0]
    exact div_le_div_of_nonneg_right he hs.le
  refine ⟨by unfold stdNormalPDF; positivity, hu, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hu), stdNormalPDF, h0]
  calc
    _ = (1 - Real.exp (-u ^ 2 / 2)) / Real.sqrt (2 * Real.pi) := by ring
    _ ≤ (u ^ 2 / 2) / Real.sqrt (2 * Real.pi) :=
      div_le_div_of_nonneg_right (by linarith) hs.le
    _ = _ := by ring

theorem kernel_integrable (q d : ℝ) :
    Integrable (fun u : ℝ => stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0) := by
  apply (integrable_stdNormalPDF.mul_const (Real.exp d)).mono'
    ((continuous_stdNormalPDF.mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with u
  change ‖stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (density_bounds u).1 (le_max_right _ _))]
  apply mul_le_mul_of_nonneg_left _ (density_bounds u).1
  exact max_le (by linarith [Real.cosh_pos (q * u)]) (Real.exp_pos d).le

private theorem cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := D5.S3.Zeros.Jensen.FactorialJensenKernelBound.even_sum_le_cosh
    2 (x ^ 2) (sq_nonneg x)
  simpa [D5.S3.Zeros.Jensen.FactorialJensenKernelBound.evenFactorialSum,
    Fin.sum_univ_two, Real.sqrt_sq_eq_abs, Real.cosh_abs] using h

private theorem exp_remainder {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    |Real.exp d - 1 - d| ≤ d ^ 2 := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd] using
    Real.norm_exp_sub_one_sub_id_le (show ‖d‖ ≤ 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hd])

private theorem cosh_remainder {x : ℝ} (hx : x ^ 2 / 2 ≤ 1) :
    |Real.cosh x - 1 - x ^ 2 / 2| ≤ x ^ 4 / 4 := by
  have h := exp_remainder (show 0 ≤ x ^ 2 / 2 by positivity) hx
  rw [abs_of_nonneg (by linarith [cosh_quadratic_lower x])]
  have hu := Real.cosh_le_exp_half_sq x
  nlinarith [(abs_le.mp h).2]

private theorem clipped_remainder {d x : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1 / 4)
    (hx : x ^ 2 ≤ 4 * d) :
    |max (Real.exp d - Real.cosh x) 0 - max (d - x ^ 2 / 2) 0| ≤ 5 * d ^ 2 := by
  have he := exp_remainder hd (by linarith)
  have hc := cosh_remainder (x := x) (by nlinarith)
  have h4 : x ^ 4 ≤ 16 * d ^ 2 := by nlinarith [sq_nonneg (x ^ 2 - 4 * d)]
  calc
    _ ≤ |(Real.exp d - Real.cosh x) - (d - x ^ 2 / 2)| :=
      abs_max_sub_max_le_abs _ _ _
    _ = |(Real.exp d - 1 - d) - (Real.cosh x - 1 - x ^ 2 / 2)| := by congr 1; ring
    _ ≤ |Real.exp d - 1 - d| + |Real.cosh x - 1 - x ^ 2 / 2| := abs_sub _ _
    _ ≤ 5 * d ^ 2 := by linarith

private theorem local_kernel_error {lo q d u : ℝ} (hlo : 0 < lo) (hq : lo ≤ q)
    (hd : 0 ≤ d) (hd1 : d ≤ 1 / 4) (hu : (q * u) ^ 2 ≤ 4 * d) :
    |stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0 -
      stdNormalPDF 0 * max (d - (q * u) ^ 2 / 2) 0| ≤
        (stdNormalPDF 0 * (5 + 2 / lo ^ 2)) * d ^ 2 := by
  have hphi := density_bounds u
  have hphi0 := (density_bounds 0).1
  have hclip := clipped_remainder hd hd1 hu
  have hqs : lo ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hlo.le hq 2
  have hus : lo ^ 2 * u ^ 2 ≤ 4 * d := by
    have := mul_le_mul_of_nonneg_right hqs (sq_nonneg u)
    nlinarith [hu]
  have hu2 : u ^ 2 ≤ 4 * d / lo ^ 2 := (le_div_iff₀ (sq_pos_of_pos hlo)).2 (by nlinarith)
  have hb : 0 ≤ max (d - (q * u) ^ 2 / 2) 0 := le_max_right _ _
  have hbd : max (d - (q * u) ^ 2 / 2) 0 ≤ d :=
    max_le (by nlinarith [sq_nonneg (q * u)]) hd
  calc
    _ = |stdNormalPDF u *
        (max (Real.exp d - Real.cosh (q * u)) 0 - max (d - (q * u) ^ 2 / 2) 0) +
        (stdNormalPDF u - stdNormalPDF 0) * max (d - (q * u) ^ 2 / 2) 0| := by congr 1; ring
    _ ≤ |stdNormalPDF u *
        (max (Real.exp d - Real.cosh (q * u)) 0 - max (d - (q * u) ^ 2 / 2) 0)| +
        |(stdNormalPDF u - stdNormalPDF 0) * max (d - (q * u) ^ 2 / 2) 0| := abs_add_le _ _
    _ = stdNormalPDF u *
        |max (Real.exp d - Real.cosh (q * u)) 0 - max (d - (q * u) ^ 2 / 2) 0| +
        |stdNormalPDF u - stdNormalPDF 0| * max (d - (q * u) ^ 2 / 2) 0 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hphi.1, abs_of_nonneg hb]
    _ ≤ stdNormalPDF 0 * (5 * d ^ 2) + (stdNormalPDF 0 * (u ^ 2 / 2)) * d := by
      exact add_le_add (mul_le_mul hphi.2.1 hclip (abs_nonneg _) hphi0)
        (mul_le_mul hphi.2.2 hbd hb (by positivity))
    _ ≤ (stdNormalPDF 0 * (5 + 2 / lo ^ 2)) * d ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hu2 (mul_nonneg hphi0 hd)
      calc
        _ ≤ stdNormalPDF 0 * (5 * d ^ 2) + (4 * d / lo ^ 2) * (stdNormalPDF 0 * d) / 2 := by
          nlinarith [hh]
        _ = _ := by ring

private theorem mem_interval_of_sq_lt {q u r : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (hu : (q * u) ^ 2 < r ^ 2) : u ∈ Ioc (-(r / q)) (r / q) := by
  have ha : |q * u| < r := (sq_lt_sq₀ (abs_nonneg _) hr).1 (by simpa only [sq_abs] using hu)
  have hh := abs_lt.mp ha
  constructor
  · rw [← neg_div]
    apply (div_lt_iff₀ hq).2
    nlinarith [hh.1]
  · apply le_of_lt
    apply (lt_div_iff₀ hq).2
    nlinarith [hh.2]

private theorem actual_support {q d : ℝ} (hq : 0 < q) (hd : 0 ≤ d) (hd1 : d ≤ 1 / 4) :
    Function.support (fun u : ℝ =>
      stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0) ⊆
        Ioc (-(2 * Real.sqrt d / q)) (2 * Real.sqrt d / q) := by
  intro u hu
  have hn := (mul_ne_zero_iff.mp hu).2
  have hp : 0 < Real.exp d - Real.cosh (q * u) :=
    lt_of_not_ge (fun h => hn (max_eq_right h))
  have he := (abs_le.mp (exp_remainder hd (by linarith : d ≤ 1))).2
  have hd2 : d ^ 2 ≤ d := by nlinarith
  apply mem_interval_of_sq_lt hq (by positivity)
  nlinarith [cosh_quadratic_lower (q * u), Real.sq_sqrt hd]

private theorem parabola_support {q d : ℝ} (hq : 0 < q) (hd : 0 ≤ d) :
    Function.support (fun u : ℝ => max (d - (q * u) ^ 2 / 2) 0) ⊆
      Ioc (-(Real.sqrt (2 * d) / q)) (Real.sqrt (2 * d) / q) := by
  intro u hu
  have hp : 0 < d - (q * u) ^ 2 / 2 :=
    lt_of_not_ge (fun h => hu (max_eq_right h))
  apply mem_interval_of_sq_lt hq (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  linarith

private theorem parabola_nonneg {q d u : ℝ} (hq : 0 < q) (hd : 0 ≤ d)
    (hu : u ∈ Icc (-(Real.sqrt (2 * d) / q)) (Real.sqrt (2 * d) / q)) :
    0 ≤ d - (q * u) ^ 2 / 2 := by
  have h1 : -Real.sqrt (2 * d) ≤ q * u := by
    have h := (div_le_iff₀ hq).1
      (show -Real.sqrt (2 * d) / q ≤ u by rw [neg_div]; exact hu.1)
    nlinarith
  have h2 : q * u ≤ Real.sqrt (2 * d) := by
    have h := (le_div_iff₀ hq).1 hu.2
    nlinarith
  have hsq := sq_le_sq₀ (abs_nonneg (q * u)) (Real.sqrt_nonneg (2 * d)) |>.2
    (abs_le.mpr ⟨h1, h2⟩)
  rw [sq_abs, Real.sq_sqrt (by positivity)] at hsq
  linarith

private theorem sqrt_mul_rpow {d : ℝ} (hd : 0 < d) :
    Real.sqrt d * d = d ^ (3 / 2 : ℝ) := by
  calc
    _ = d ^ (1 / 2 : ℝ) * d ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
    _ = d ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hd _ _).symm
    _ = _ := by norm_num

private theorem parabola_integral {q d : ℝ} (hq : 0 < q) (hd : 0 < d) :
    (∫ u : ℝ, max (d - (q * u) ^ 2 / 2) 0) =
      (4 * Real.sqrt 2 / (3 * q)) * d ^ (3 / 2 : ℝ) := by
  let r := Real.sqrt (2 * d) / q
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : (Real.sqrt (2 * d)) ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  have hint : (∫ u in -r..r, d - (q * u) ^ 2 / 2) =
      2 * d * r - q ^ 2 * (2 * r ^ 3 / 3) / 2 := by
    have hf : (fun u : ℝ => d - (q * u) ^ 2 / 2) =
        (fun u : ℝ => d - (q ^ 2 / 2) * u ^ 2) := by ext u; ring
    rw [hf, intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun _ : ℝ => d)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun u : ℝ => (q ^ 2 / 2) * u ^ 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_pow]
    simp only [smul_eq_mul]
    ring
  calc
    _ = ∫ u in -r..r, max (d - (q * u) ^ 2 / 2) 0 :=
      (intervalIntegral.integral_eq_integral_of_support_subset (parabola_support hq hd.le)).symm
    _ = ∫ u in -r..r, d - (q * u) ^ 2 / 2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by linarith : -r ≤ r)] at hu
      exact max_eq_left (parabola_nonneg hq hd.le hu)
    _ = 2 * d * r - q ^ 2 * (2 * r ^ 3 / 3) / 2 := hint
    _ = (4 / (3 * q)) * (Real.sqrt (2 * d) * d) := by
      dsimp [r]
      field_simp
      nlinarith [hs]
    _ = (4 * Real.sqrt 2 / (3 * q)) * d ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← sqrt_mul_rpow hd]
      ring

private theorem parabola_support_wide {q d : ℝ} (hq : 0 < q) (hd : 0 ≤ d) :
    Function.support (fun u : ℝ =>
      stdNormalPDF 0 * max (d - (q * u) ^ 2 / 2) 0) ⊆
        Ioc (-(2 * Real.sqrt d / q)) (2 * Real.sqrt d / q) := by
  intro u hu
  have hu' := parabola_support hq hd ((mul_ne_zero_iff.mp hu).2)
  have hs : Real.sqrt (2 * d) ≤ 2 * Real.sqrt d := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * d by positivity), Real.sq_sqrt hd,
      Real.sqrt_nonneg (2 * d), Real.sqrt_nonneg d]
  have hb := div_le_div_of_nonneg_right hs hq.le
  exact ⟨lt_of_le_of_lt (neg_le_neg hb) hu'.1, hu'.2.trans hb⟩

private theorem sqrt_mul_sq_rpow {d : ℝ} (hd : 0 < d) :
    Real.sqrt d * d ^ 2 = d ^ (5 / 2 : ℝ) := by
  calc
    _ = d ^ (1 / 2 : ℝ) * d ^ (2 : ℝ) := by
      simp [Real.sqrt_eq_rpow]
    _ = d ^ ((1 / 2 : ℝ) + 2) := (Real.rpow_add hd _ _).symm
    _ = _ := by norm_num

private theorem integral_error {lo q d : ℝ} (hlo : 0 < lo) (hq : lo ≤ q)
    (hd : 0 < d) (hd1 : d ≤ 1 / 4) :
    |gaussianCoshIntegral q d -
      (4 * Real.sqrt 2 * stdNormalPDF 0 / (3 * q)) * d ^ (3 / 2 : ℝ)| ≤
        (4 * (stdNormalPDF 0 * (5 + 2 / lo ^ 2)) / lo) * d ^ (5 / 2 : ℝ) := by
  let f := fun u : ℝ => stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0
  let g := fun u : ℝ => stdNormalPDF 0 * max (d - (q * u) ^ 2 / 2) 0
  let R := 2 * Real.sqrt d / q
  let K := stdNormalPDF 0 * (5 + 2 / lo ^ 2)
  have hq0 : 0 < q := hlo.trans_le hq
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hK : 0 ≤ K := mul_nonneg (density_bounds 0).1 (by positivity)
  have hf : Continuous f := continuous_stdNormalPDF.mul (by fun_prop)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hfR : (∫ u in -R..R, f u) = ∫ u, f u :=
    intervalIntegral.integral_eq_integral_of_support_subset (actual_support hq0 hd.le hd1)
  have hgR : (∫ u in -R..R, g u) = ∫ u, g u :=
    intervalIntegral.integral_eq_integral_of_support_subset (parabola_support_wide hq0 hd.le)
  have hgval : (∫ u, g u) =
      (4 * Real.sqrt 2 * stdNormalPDF 0 / (3 * q)) * d ^ (3 / 2 : ℝ) := by
    dsimp [g]
    rw [integral_const_mul, parabola_integral hq0 hd]
    ring
  have heq : gaussianCoshIntegral q d -
      (4 * Real.sqrt 2 * stdNormalPDF 0 / (3 * q)) * d ^ (3 / 2 : ℝ) =
        ∫ u in -R..R, f u - g u := by
    change (∫ u, f u) - _ = _
    rw [← hgval, ← hfR, ← hgR,
      intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  rw [heq]
  have hbound : ∀ u ∈ Set.uIoc (-R) R, ‖f u - g u‖ ≤ K * d ^ 2 := by
    intro u hu
    rw [uIoc_of_le (by linarith : -R ≤ R)] at hu
    have hl : -(2 * Real.sqrt d) ≤ q * u := by
      have hh := (div_le_iff₀ hq0).1
        (show -(2 * Real.sqrt d) / q ≤ u by rw [neg_div]; exact hu.1.le)
      nlinarith
    have hr : q * u ≤ 2 * Real.sqrt d := by
      have hh := (le_div_iff₀ hq0).1 hu.2
      nlinarith
    have hsq := (sq_le_sq₀ (abs_nonneg (q * u))
      (show 0 ≤ 2 * Real.sqrt d by positivity)).2 (abs_le.mpr ⟨hl, hr⟩)
    have hu2 : (q * u) ^ 2 ≤ 4 * d := by
      nlinarith [Real.sq_sqrt hd.le, sq_abs (q * u)]
    simpa only [Real.norm_eq_abs] using local_kernel_error hlo hq hd.le hd1 hu2
  calc
    _ ≤ K * d ^ 2 * |R - -R| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = (4 * K / q) * (Real.sqrt d * d ^ 2) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ R - -R)]
      dsimp [R]
      ring
    _ ≤ (4 * K / lo) * (Real.sqrt d * d ^ 2) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hlo hq)
        (by positivity)
    _ = _ := by rw [sqrt_mul_sq_rpow hd]

/-- The exact local kernel expansion is uniform on every positive compact interval.
The assertion also covers empty intervals; in particular no strict width is required. -/
theorem gaussian_cosh_uniform_remainder (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ q ∈ Icc lo hi, ∀ d : ℝ, 0 < d → d ≤ δ →
        Integrable (fun u : ℝ =>
          stdNormalPDF u * max (Real.exp d - Real.cosh (q * u)) 0) ∧
        |gaussianCoshIntegral q d -
          (4 * Real.sqrt 2 * stdNormalPDF 0 / (3 * q)) * d ^ (3 / 2 : ℝ)| ≤
            C * d ^ (5 / 2 : ℝ) := by
  have hphi0 : 0 ≤ stdNormalPDF 0 := (density_bounds 0).1
  refine ⟨1 / 4, 4 * (stdNormalPDF 0 * (5 + 2 / lo ^ 2)) / lo,
    by norm_num, by positivity, ?_⟩
  intro q hq d hd hd1
  exact ⟨kernel_integrable q d, integral_error hlo hq.1 hd hd1⟩

end D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
