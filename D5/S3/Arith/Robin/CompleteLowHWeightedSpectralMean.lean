/- GID: D5/S3/Arith/Robin/CompleteLowHWeightedSpectralMean
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/CompleteLowHWeightedSpectralMean
   mirror-E: none(waiver:analytic identity and bounds have no numeric evidence projection)
   anchors: []
   utility: none
   digest: Divided cubic estimates and the complete weighted low-height mean bound.

   For arbitrary CompleteZeroFamily, m >= 1 and gamma > 10, the norm bound is
     m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)).
   This owner proves the divided-polynomial core 20, integrated coefficient
   240, absolute shell-norm summability, and both physical extension estimates.
   The full h-window Icc 0 2 has weight 1+h and integral 4; the Gaussian center
   is 16*m and the physical coefficient is 3. Multiplicity and both signs stay
   in the countable sums. The full-line identity is supplied by the Gaussian
   mean owner; no final bound or critical-line hypothesis is assumed.
-/
import D5.S3.Arith.Robin.CompleteLowHWeightedGaussianMean

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
open scoped BigOperators NNReal ENNReal

namespace D5.S3.Arith.Robin.CompleteLowHWeightedSpectralMean

set_option autoImplicit false

private lemma resolvent_denominator_ne_zero_of_height
    (ρ : ℂ) (h : ℝ) (hρ : 10 < |ρ.im|) :
    ρ * (1 + h - ρ) ≠ 0 := by
  have hi : ρ.im ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hρ
    linarith
  apply mul_ne_zero
  · intro he
    exact hi (by simpa using congrArg Complex.im he)
  · intro he
    have he' := congrArg Complex.im he
    simp at he'
    have : ρ.im = 0 := by linarith
    exact hi this

private lemma resolvent_norm_le_abs_im_sq_inv
    (ρ : ℂ) (h : ℝ) (hρ : 10 < |ρ.im|) :
    ‖resolventCoefficient ρ h‖ ≤ (|ρ.im| ^ 2)⁻¹ := by
  have ht : 0 < |ρ.im| := by linarith
  have hden := resolvent_denominator_ne_zero_of_height ρ h hρ
  have hp : 0 < ‖ρ‖ * ‖(1 + h - ρ : ℂ)‖ := by
    simpa only [norm_mul] using norm_pos_iff.mpr hden
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm _
  have h2 : |ρ.im| ≤ ‖(1 + h - ρ : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (1 + h - ρ : ℂ)
  have hprod : |ρ.im| ^ 2 ≤ ‖ρ‖ * ‖(1 + h - ρ : ℂ)‖ := by
    simpa only [pow_two] using mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  rw [resolventCoefficient, norm_inv, norm_mul]
  exact (inv_le_inv₀ hp (sq_pos_of_pos ht)).mpr hprod

/-- A genuine bound stronger than the paper's core 20.  First divide by the
    actual complex denominator.  With t=|Im ρ|>10, |Re ρ-h|≤2 gives
    ‖z‖≤2t, ‖16m+2mz+1‖≤6mt and ‖z²+γ²+1+1/(2m)‖≤4t²+D².
    The three numerator terms 24mt³, 6mD²t, 4t are each paid explicitly
    before cancelling t².  Neither sign of Im ρ is selected. -/
private theorem divided_cubic_polynomial_bound_two
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖resolventCoefficient ρ h * cubicPolynomial m γ (ρ - h)‖ ≤
      2 * m * D γ ^ 2 * (|ρ.im| + 1) := by
  let t : ℝ := |ρ.im|
  let z : ℂ := ρ - h
  have ht : 10 < t := hheight
  have ht0 : 0 < t := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hd24 : 24 ≤ D γ ^ 2 := by dsimp [D]; nlinarith
  have hdγ : γ ^ 2 + 2 ≤ D γ ^ 2 := by dsimp [D]; nlinarith
  have hmd : 1 ≤ m * D γ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (sq_nonneg (D γ))
    nlinarith only [this, hd24]
  have hzre : |z.re| ≤ 2 := by
    apply abs_le.mpr
    dsimp [z]
    constructor <;> linarith [hstrip.1, hstrip.2, hh.1, hh.2]
  have hzim : |z.im| = t := by simp [z, t]
  have hz : ‖z‖ ≤ 2 * t := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [hzim] at this
    linarith
  have hnm : ‖(m : ℂ)‖ = m := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  have hnc : ‖(centre m : ℂ)‖ = 16 * m := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ centre m by dsimp [centre]; positivity)]
    rfl
  have hA : ‖(centre m : ℂ) + 2 * m * z + 1‖ ≤ 6 * m * t := by
    calc
      _ ≤ ‖(centre m : ℂ)‖ + ‖(2 : ℂ) * m * z‖ + ‖(1 : ℂ)‖ :=
        norm_add₃_le
      _ = 16 * m + 2 * m * ‖z‖ + 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_one]
        rw [abs_of_nonneg hm0]
        dsimp [centre]
        rw [abs_of_nonneg (by positivity : 0 ≤ 16 * m)]
        norm_num
      _ ≤ 16 * m + 2 * m * (2 * t) + 1 := by gcongr
      _ ≤ 6 * m * t := by
        have hmt : 10 * m ≤ m * t :=
          (by simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left (by linarith : (10 : ℝ) ≤ t) hm0))
        nlinarith only [hmt, hm]
  have hfrac : ‖(1 : ℂ) / (2 * m)‖ ≤ 1 := by
    have he : ‖(1 : ℂ) / (2 * m)‖ = 1 / (2 * m) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hm0]
      norm_num
    rw [he]
    exact (div_le_one (by linarith : 0 < 2 * m)).mpr (by linarith)
  have hng : ‖(γ : ℂ) ^ 2‖ = γ ^ 2 := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hB : ‖z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * m)‖ ≤
      4 * t ^ 2 + D γ ^ 2 := by
    calc
      _ ≤ ‖z ^ 2 + (γ : ℂ) ^ 2 + 1‖ + ‖(1 : ℂ) / (2 * m)‖ :=
        norm_add_le _ _
      _ ≤ (‖z ^ 2‖ + ‖(γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖) +
          ‖(1 : ℂ) / (2 * m)‖ := by
        have htri : ‖z ^ 2 + (γ : ℂ) ^ 2 + 1‖ ≤
            ‖z ^ 2‖ + ‖(γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖ := by
          calc
            _ ≤ ‖z ^ 2 + (γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ ≤ (‖z ^ 2‖ + ‖(γ : ℂ) ^ 2‖) + ‖(1 : ℂ)‖ := by
              exact add_le_add (norm_add_le _ _) (le_refl _)
        exact add_le_add htri (le_refl _)
      _ ≤ (2 * t) ^ 2 + γ ^ 2 + 1 + 1 := by
        rw [norm_pow, hng, norm_one]
        exact add_le_add (by gcongr) hfrac
      _ ≤ 4 * t ^ 2 + D γ ^ 2 := by nlinarith only [hdγ]
  have hP : ‖cubicPolynomial m γ z‖ ≤
      (6 * m * t) * (4 * t ^ 2 + D γ ^ 2) + 4 * t := by
    unfold cubicPolynomial
    calc
      _ ≤ ‖((centre m : ℂ) + 2 * m * z + 1) *
            (z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * m))‖ + ‖(2 : ℂ) * z‖ :=
        norm_add_le _ _
      _ = ‖(centre m : ℂ) + 2 * m * z + 1‖ *
          ‖z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * m)‖ + 2 * ‖z‖ := by
        simp [norm_mul]
      _ ≤ (6 * m * t) * (4 * t ^ 2 + D γ ^ 2) + 4 * t := by
        exact add_le_add
          (mul_le_mul hA hB (norm_nonneg _) (by positivity))
          (by linarith)
  have hN1 : (6 * m * t) * (4 * t ^ 2) ≤
      (m * D γ ^ 2 * t) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hd24
      (show 0 ≤ m * t * t ^ 2 by positivity)
    nlinarith only [this]
  have hN2 : (6 * m * t) * D γ ^ 2 ≤ (m * D γ ^ 2) * t ^ 2 := by
    have ht6 : 6 * t ≤ t ^ 2 := by
      nlinarith [mul_nonneg ht0.le (by linarith : 0 ≤ t - 6)]
    have := mul_le_mul_of_nonneg_left ht6
      (show 0 ≤ m * D γ ^ 2 by positivity)
    nlinarith only [this]
  have hN3 : 4 * t ≤ (m * D γ ^ 2) * t ^ 2 := by
    have ht4 : 4 * t ≤ t ^ 2 := by
      nlinarith [mul_nonneg ht0.le (by linarith : 0 ≤ t - 4)]
    exact ht4.trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hmd (sq_nonneg t)])
  have hN : (6 * m * t) * (4 * t ^ 2 + D γ ^ 2) + 4 * t ≤
      (2 * m * D γ ^ 2 * (t + 1)) * t ^ 2 := by
    calc
      _ = (6 * m * t) * (4 * t ^ 2) + (6 * m * t) * D γ ^ 2 + 4 * t := by ring
      _ ≤ (m * D γ ^ 2 * t) * t ^ 2 +
          (m * D γ ^ 2) * t ^ 2 + (m * D γ ^ 2) * t ^ 2 :=
        add_le_add (add_le_add hN1 hN2) hN3
      _ = m * D γ ^ 2 * (t + 2) * t ^ 2 := by ring
      _ ≤ (2 * m * D γ ^ 2 * (t + 1)) * t ^ 2 := by
        have hp : 0 ≤ m * D γ ^ 2 * t * t ^ 2 := by positivity
        nlinarith only [hp]
  rw [norm_mul]
  change ‖resolventCoefficient ρ h‖ * ‖cubicPolynomial m γ z‖ ≤
    2 * m * D γ ^ 2 * (t + 1)
  calc
    _ ≤ (t ^ 2)⁻¹ * ‖cubicPolynomial m γ z‖ :=
      mul_le_mul_of_nonneg_right (resolvent_norm_le_abs_im_sq_inv ρ h hheight)
        (norm_nonneg _)
    _ ≤ (t ^ 2)⁻¹ * ((2 * m * D γ ^ 2 * (t + 1)) * t ^ 2) :=
      mul_le_mul_of_nonneg_left (hP.trans hN) (by positivity)
    _ = 2 * m * D γ ^ 2 * (t + 1) := by
      field_simp [ne_of_gt ht0] <;> ring

/-- Original-paper divided-polynomial core estimate, for arbitrary complex ρ
    in the full strip and both signed heights. -/
theorem divided_cubic_polynomial_bound
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖resolventCoefficient ρ h * cubicPolynomial m γ (ρ - h)‖ ≤
      20 * m * D γ ^ 2 * (|ρ.im| + 1) := by
  have hm0 : 0 ≤ m := by linarith
  refine (divided_cubic_polynomial_bound_two m γ ρ h hm hγ hstrip hheight hh).trans ?_
  gcongr <;> norm_num

private lemma divided_cubic_exponential_bound
    (m : ℝ) (ρ : ℂ) (h : ℝ) (hm : 1 ≤ m)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖Complex.exp (m * (ρ - h) ^ 2 + centre m * (ρ - h))‖ ≤
      Real.exp (17 * m) * Real.exp (-m * ρ.im ^ 2) := by
  have hm0 : 0 ≤ m := by linarith
  have hxlo : -2 ≤ ρ.re - h := by linarith [hstrip.1, hh.2]
  have hxhi : ρ.re - h ≤ 1 := by linarith [hstrip.2, hh.1]
  have hquad : (ρ.re - h) ^ 2 + 16 * (ρ.re - h) ≤ 17 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (ρ.re - h))
      (by linarith : 0 ≤ 17 + (ρ.re - h))]
  have heq : (m * (ρ - h) ^ 2 + centre m * (ρ - h) : ℂ).re =
      m * ((ρ.re - h) ^ 2 - ρ.im ^ 2) + 16 * m * (ρ.re - h) := by
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    dsimp [centre]
    ring
  rw [Complex.norm_exp, heq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hquad hm0]

private theorem divided_cubic_coefficient_core_two
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖dividedCubicCoefficient m γ ρ h‖ ≤
      2 * m * D γ ^ 2 * shellWeight m ρ * Real.exp (17 * m) := by
  rw [dividedCubicCoefficient, ← mul_assoc, norm_mul]
  calc
    _ ≤ (2 * m * D γ ^ 2 * (|ρ.im| + 1)) *
        (Real.exp (17 * m) * Real.exp (-m * ρ.im ^ 2)) :=
      mul_le_mul
        (divided_cubic_polynomial_bound_two m γ ρ h hm hγ hstrip hheight hh)
        (divided_cubic_exponential_bound m ρ h hm hstrip hh)
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold shellWeight; ring

theorem divided_cubic_coefficient_core_bound
    (m γ : ℝ) (ρ : ℂ) (h : ℝ)
    (hm : 1 ≤ m) (hγ : 10 < γ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hheight : 10 < |ρ.im|)
    (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖dividedCubicCoefficient m γ ρ h‖ ≤
      20 * m * D γ ^ 2 * shellWeight m ρ * Real.exp (17 * m) := by
  rw [dividedCubicCoefficient, ← mul_assoc, norm_mul]
  calc
    _ ≤ (20 * m * D γ ^ 2 * (|ρ.im| + 1)) *
        (Real.exp (17 * m) * Real.exp (-m * ρ.im ^ 2)) :=
      mul_le_mul
        (divided_cubic_polynomial_bound m γ ρ h hm hγ hstrip hheight hh)
        (divided_cubic_exponential_bound m ρ h hm hstrip hh)
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold shellWeight; ring

/-- The actual whole-prefactor pointwise bound supplies the finite majorant
    for Bochner integrability. -/
theorem divided_coefficient_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) (h : ℝ) (hh : h ∈ Icc (0 : ℝ) 2) :
    ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
        dividedCubicCoefficient m γ (Z.zero n) h‖ ≤
      240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  have hw : ‖((1 + h : ℝ) : ℂ)‖ = 1 + h := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hh.1])]
  have hm0 : 0 ≤ m := by linarith
  have hs0 : 0 ≤ shellWeight m (Z.zero n) := by unfold shellWeight; positivity
  calc
    _ = 3 * (1 + h) * ‖dividedCubicCoefficient m γ (Z.zero n) h‖ := by
      simp only [norm_mul, hw]
      norm_num
    _ ≤ 3 * (1 + h) *
        (20 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m)) :=
      mul_le_mul_of_nonneg_left
        (divided_cubic_coefficient_core_bound m γ (Z.zero n) h hm hγ
          (Z.strip n) (Z.height n) hh) (by linarith [hh.1])
    _ ≤ 240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
      have hp : 0 ≤ m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) :=
        by positivity
      have hh' : 3 * (1 + h) * 20 ≤ (240 : ℝ) := by linarith [hh.2]
      nlinarith [mul_le_mul_of_nonneg_right hh' hp]

private lemma divided_cubic_coefficient_continuous
    (m γ : ℝ) (ρ : ℂ) (hheight : 10 < |ρ.im|) :
    Continuous (dividedCubicCoefficient m γ ρ) := by
  have hd : Continuous (fun h : ℝ => ρ * (1 + h - ρ)) := by fun_prop
  have hr : Continuous (fun h : ℝ => resolventCoefficient ρ h) :=
    hd.inv₀ (fun h => resolvent_denominator_ne_zero_of_height ρ h hheight)
  have hp : Continuous (fun h : ℝ => cubicPolynomial m γ (ρ - h) *
      Complex.exp (m * (ρ - h) ^ 2 + centre m * (ρ - h))) := by
    unfold cubicPolynomial
    fun_prop
  exact hr.mul hp

theorem shell_term_integrable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) :
    IntegrableOn (fun h => (3 : ℂ) * ((1 + h : ℝ) : ℂ) *
      dividedCubicCoefficient m γ (Z.zero n) h) (Icc (0 : ℝ) 2) := by
  have hc : Continuous (fun h : ℝ => (3 : ℂ) * ((1 + h : ℝ) : ℂ) *
      dividedCubicCoefficient m γ (Z.zero n) h) := by
    exact (by fun_prop : Continuous (fun h : ℝ => (3 : ℂ) * ((1 + h : ℝ) : ℂ))).mul
      (divided_cubic_coefficient_continuous m γ (Z.zero n) (Z.height n))
  have hi : IntegrableOn (fun _h : ℝ =>
      240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m))
      (Icc (0 : ℝ) 2) := continuous_const.integrableOn_Icc
  refine Integrable.mono' hi hc.aestronglyMeasurable ?_
  exact (ae_restrict_mem measurableSet_Icc).mono fun h hh =>
    divided_coefficient_bound Z m γ hm hγ n h hh

private lemma h_weight_integral :
    (∫ h in Icc (0 : ℝ) 2, (1 + h)) = 4 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (∫ h in (0 : ℝ)..2, (1 + h)) =
        (∫ _h in (0 : ℝ)..2, (1 : ℝ)) + (∫ h in (0 : ℝ)..2, h) :=
      intervalIntegral.integral_add
        (continuous_const.intervalIntegrable 0 2)
        (continuous_id.intervalIntegrable 0 2)
    _ = 4 := by norm_num [intervalIntegral.integral_const, integral_id]

/- This internal integration lemma has actual pointwise evidence as a proof
   argument at each call below.  No coefficient premise is exposed in the
   final certificate.  In particular it integrates 3*(1+h), whose integral
   is 12; it does not integrate a whole-prefactor 240 into a spurious 24. -/
private lemma shell_term_bound_of_core
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) (c : ℝ)
    (hcore : ∀ h, h ∈ Icc (0 : ℝ) 2 →
      ‖dividedCubicCoefficient m γ (Z.zero n) h‖ ≤
        c * shellWeight m (Z.zero n) * Real.exp (17 * m)) :
    ‖shellTerm Z m γ n‖ ≤
      12 * c * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  let B : ℝ := c * shellWeight m (Z.zero n) * Real.exp (17 * m)
  have hi := shell_term_integrable Z m γ hm hγ n
  have hg : IntegrableOn (fun h : ℝ => 3 * (1 + h) * B) (Icc (0 : ℝ) 2) := by
    exact (by fun_prop : Continuous (fun h : ℝ => 3 * (1 + h) * B)).integrableOn_Icc
  have hnorm : ∀ᵐ h ∂volume.restrict (Icc (0 : ℝ) 2),
      ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
        dividedCubicCoefficient m γ (Z.zero n) h‖ ≤ 3 * (1 + h) * B := by
    exact (ae_restrict_mem measurableSet_Icc).mono fun h hh => by
      have hw : ‖((1 + h : ℝ) : ℂ)‖ = 1 + h := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hh.1])]
      have he : ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
          dividedCubicCoefficient m γ (Z.zero n) h‖ =
          3 * (1 + h) * ‖dividedCubicCoefficient m γ (Z.zero n) h‖ := by
        simp only [norm_mul, hw]
        norm_num
      rw [he]
      exact mul_le_mul_of_nonneg_left (hcore h hh) (by linarith [hh.1])
  calc
    ‖shellTerm Z m γ n‖ ≤ ∫ h in Icc (0 : ℝ) 2,
        ‖(3 : ℂ) * ((1 + h : ℝ) : ℂ) *
          dividedCubicCoefficient m γ (Z.zero n) h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Icc (0 : ℝ) 2, 3 * (1 + h) * B := integral_mono_ae hi.norm hg hnorm
    _ = (3 * B) * (∫ h in Icc (0 : ℝ) 2, (1 + h)) := by
      calc
        _ = ∫ h in Icc (0 : ℝ) 2, (3 * B) * (1 + h) := by
          apply integral_congr_ae
          exact ae_of_all _ fun h => by ring
        _ = _ := by rw [integral_const_mul]
    _ = 12 * c * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
      rw [h_weight_integral]
      dsimp [B]
      ring

/-- The paper's actual integrated coefficient, 3*4*20=240. -/
theorem shell_term_bound240
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) :
    ‖shellTerm Z m γ n‖ ≤
      240 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  have hb := shell_term_bound_of_core Z m γ hm hγ n (20 * m * D γ ^ 2)
    (fun h hh => divided_cubic_coefficient_core_bound m γ (Z.zero n) h hm hγ
      (Z.strip n) (Z.height n) hh)
  convert hb using 1 <;> ring

/-- The stronger integrated bound uses the divided-polynomial core 2 and
    the exact weight integral, giving 3*4*2=24. -/
theorem shell_term_bound24
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (n : ZeroIndex) :
    ‖shellTerm Z m γ n‖ ≤
      24 * m * D γ ^ 2 * shellWeight m (Z.zero n) * Real.exp (17 * m) := by
  have hb := shell_term_bound_of_core Z m γ hm hγ n (2 * m * D γ ^ 2)
    (fun h hh => divided_cubic_coefficient_core_two m γ (Z.zero n) h hm hγ
      (Z.strip n) (Z.height n) hh)
  convert hb using 1 <;> ring

/-- Comparison of the actual full complex shell norms with the already
    proved all-index shell series.  No convergence field or finite-family
    restriction is assumed, and no default value of tsum is invoked. -/
theorem shell_terms_norm_summable
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    Summable (fun n => ‖shellTerm Z m γ n‖) := by
  let c : ℝ := 24 * m * D γ ^ 2 * Real.exp (17 * m)
  have hs := (shell_summable_and_count_bound Z m hm).1.mul_left c
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hs
  intro n
  simpa [c, mul_assoc, mul_left_comm, mul_comm] using shell_term_bound24 Z m γ hm hγ n

/-- Actual full-complex series consumer of the integrated paper bound. -/
theorem complete_real_line_mean_bound240
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖completeRealLineMean Z m γ‖ ≤
      240 * m * D γ ^ 2 * shellSum Z m * Real.exp (17 * m) := by
  let c : ℝ := 240 * m * D γ ^ 2 * Real.exp (17 * m)
  have hs := (shell_summable_and_count_bound Z m hm).1
  have hc : HasSum (fun n => c * shellWeight m (Z.zero n))
      (c * shellSum Z m) := by
    simpa [shellSum] using hs.hasSum.mul_left c
  have hb : ∀ n, ‖shellTerm Z m γ n‖ ≤ c * shellWeight m (Z.zero n) := by
    intro n
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using shell_term_bound240 Z m γ hm hγ n
  have hnorm := shell_terms_norm_summable Z m γ hm hγ
  simpa [completeRealLineMean, c, mul_assoc, mul_left_comm, mul_comm] using
    hnorm.of_norm.hasSum.norm_le_of_bounded hc hb


/-! The two original extension estimates.  These helpers keep the full zero
family and use the existing scalar Gaussian moment theorem; no moment formula
is re-ported here.  All new helpers below feed the two original extensions. -/

/-- Absolute convergence is paid by the existing all-real norm series.
The sharper exponential estimate is proved separately on each actual domain. -/
private theorem extension_kernel_norm_le
    (Z : CompleteZeroFamily) (h y c : ℝ) (hh : h ∈ Icc (0 : ℝ) 2)
    (hc : 0 ≤ c)
    (he : ∀ n, ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ c) :
    ‖spectralKernel Z h y‖ ≤ c * (∑' n, ((Z.zero n).im)⁻¹ ^ 2) := by
  have hs := (zero_series_summable_and_bound Z h y hh).1
  have hn : Summable (fun n =>
      ‖Complex.exp ((Z.zero n - h) * y) * resolventCoefficient (Z.zero n) h‖) := by
    simpa only [norm_mul] using hs
  calc
    ‖spectralKernel Z h y‖ ≤
        ∑' n, ‖Complex.exp ((Z.zero n - h) * y)‖ *
          ‖resolventCoefficient (Z.zero n) h‖ := by
      simpa only [spectralKernel, norm_mul] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, c * ((Z.zero n).im)⁻¹ ^ 2 :=
      hs.tsum_le_tsum (fun n => mul_le_mul (he n)
        (resolvent_norm_le_reciprocal_square Z n h hh) (norm_nonneg _) hc)
        (Z.reciprocalSquare.mul_left c)
    _ = c * (∑' n, ((Z.zero n).im)⁻¹ ^ 2) := by rw [tsum_mul_left]

/-- Genuine fixed-y Bochner integrability on the complete h-window, followed
by the norm estimate with its exact weight integral 4 and complete R < 2. -/
private theorem extension_inner_integrable_and_bound
    (Z : CompleteZeroFamily) (y c : ℝ) (hc : 0 ≤ c)
    (he : ∀ n h, h ∈ Icc (0 : ℝ) 2 →
      ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ c) :
    IntegrableOn (fun h : ℝ => ((1 + h : ℝ) : ℂ) * spectralKernel Z h y)
      (Icc (0 : ℝ) 2) ∧
    ‖∫ h in Icc (0 : ℝ) 2, ((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ ≤ 8 * c := by
  let R : ℝ := ∑' n, ((Z.zero n).im)⁻¹ ^ 2
  have hR2 : R ≤ 2 := Z.reciprocalSquare_lt_two.le
  have hmeas : Measurable (fun h : ℝ =>
      ((1 + h : ℝ) : ℂ) * spectralKernel Z h y) := by
    have hk : Measurable (fun h : ℝ => spectralKernel Z h y) := by
      unfold spectralKernel
      apply Measurable.tsum
      intro n
      unfold resolventCoefficient
      fun_prop
    exact (by fun_prop : Measurable (fun h : ℝ => ((1 + h : ℝ) : ℂ))).mul hk
  have hmajor : IntegrableOn (fun h : ℝ => (1 + h) * (c * R))
      (Icc (0 : ℝ) 2) :=
    ((continuous_const.add continuous_id).mul continuous_const).integrableOn_Icc
  have hbound : ∀ᵐ h ∂(volume.restrict (Icc (0 : ℝ) 2)),
      ‖((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ ≤ (1 + h) * (c * R) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with h hh
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 1 + h by linarith [hh.1])]
    exact mul_le_mul_of_nonneg_left
      (extension_kernel_norm_le Z h y c hh hc (fun n => he n h hh))
      (by linarith [hh.1])
  have hint : IntegrableOn (fun h : ℝ =>
      ((1 + h : ℝ) : ℂ) * spectralKernel Z h y) (Icc (0 : ℝ) 2) :=
    hmajor.mono' hmeas.aestronglyMeasurable hbound
  refine ⟨hint, ?_⟩
  calc
    ‖∫ h in Icc (0 : ℝ) 2, ((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ ≤
        ∫ h in Icc (0 : ℝ) 2,
          ‖((1 + h : ℝ) : ℂ) * spectralKernel Z h y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Icc (0 : ℝ) 2, (1 + h) * (c * R) :=
      integral_mono_ae hint.norm hmajor hbound
    _ = 4 * (c * R) := by rw [integral_mul_const, h_weight_integral]
    _ ≤ 8 * c := by nlinarith [mul_le_mul_of_nonneg_left hR2 hc]

private theorem extension_positive_exp_le
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) (hy : y ∈ Ioc (0 : ℝ) 1) :
    ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ 3 := by
  rw [Complex.norm_exp]
  have heq : ((Z.zero n - h) * y : ℂ).re = ((Z.zero n).re - h) * y := by
    simp [Complex.mul_re]
  rw [heq]
  have hcoef : (Z.zero n).re - h ≤ 1 := by linarith [Z.strip n |>.2, hh.1]
  calc
    Real.exp (((Z.zero n).re - h) * y) ≤ Real.exp y :=
      Real.exp_le_exp.mpr (by
        simpa using mul_le_mul_of_nonneg_right hcoef hy.1.le)
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hy.2
    _ ≤ 3 := Real.exp_one_lt_three.le

private theorem extension_negative_exp_le
    (Z : CompleteZeroFamily) (n : ZeroIndex) (h y : ℝ)
    (hh : h ∈ Icc (0 : ℝ) 2) (hy : y ≤ 0) :
    ‖Complex.exp ((Z.zero n - h) * y)‖ ≤ Real.exp (-2 * y) := by
  rw [Complex.norm_exp]
  have heq : ((Z.zero n - h) * y : ℂ).re = ((Z.zero n).re - h) * y := by
    simp [Complex.mul_re]
  rw [heq]
  have hcoef : -2 ≤ (Z.zero n).re - h := by linarith [Z.strip n |>.1, hh.2]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcoef hy)

private theorem extension_density_nonneg (m y : ℝ) (hm : 0 < m) :
    0 ≤ gaussianDensity m y := by
  unfold gaussianDensity
  positivity

private theorem extension_physical_norm (m γ y : ℝ) (hm : 0 < m) :
    ‖(physicalEnvelope m γ y : ℂ)‖ =
      3 * |y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) *
        gaussianDensity m y := by
  rw [Complex.norm_real, Real.norm_eq_abs, physicalEnvelope,
    abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (show 0 ≤ gaussianCoordinate m y ^ 2 + γ ^ 2 + 1 by positivity),
    abs_of_nonneg (extension_density_nonneg m y hm)]

private theorem extension_positive_physical_le
    (m γ y : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) (hy : y ∈ Ioc (0 : ℝ) 1) :
    ‖(physicalEnvelope m γ y : ℂ)‖ ≤ 6 * D γ ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hqlo : -8 ≤ gaussianCoordinate m y := by
    unfold gaussianCoordinate centre
    apply (le_div_iff₀ (show 0 < 2 * m by positivity)).2
    linarith [hy.1]
  have hqhi : gaussianCoordinate m y ≤ 0 := by
    unfold gaussianCoordinate centre
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) (by positivity)
  have hq : gaussianCoordinate m y ^ 2 ≤ 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqlo) (neg_nonneg.mpr hqhi)]
  have hpoly : gaussianCoordinate m y ^ 2 + γ ^ 2 + 1 ≤ D γ ^ 2 := by
    unfold D
    nlinarith
  have hs : 0 < Real.sqrt (4 * Real.pi * m) := by positivity
  have hs1 : 1 ≤ Real.sqrt (4 * Real.pi * m) := by
    have hp := Real.two_le_pi
    have hmπ : Real.pi ≤ Real.pi * m := by nlinarith [Real.pi_pos]
    have hsq := Real.sq_sqrt (show 0 ≤ 4 * Real.pi * m by positivity)
    nlinarith [Real.sqrt_nonneg (4 * Real.pi * m)]
  have he : Real.exp (-(y - centre m) ^ 2 / (4 * m)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hd : gaussianDensity m y ≤ 1 := by
    unfold gaussianDensity
    apply (div_le_iff₀ hs).2
    simpa only [one_mul] using he.trans hs1
  rw [extension_physical_norm m γ y hmpos,
    abs_of_nonneg (show 0 ≤ y + 1 by linarith [hy.1])]
  calc
    3 * (y + 1) * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) * gaussianDensity m y ≤
        (6 * D γ ^ 2) * 1 := by
      apply mul_le_mul _ hd (extension_density_nonneg m y hmpos) (by positivity)
      exact mul_le_mul (by linarith [hy.2]) hpoly (by positivity) (by norm_num)
    _ = 6 * D γ ^ 2 := mul_one _

theorem complete_zero_positive_extension_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖positiveExtension Z m γ‖ ≤ 2400 * m * D γ ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hf : IntegrableOn (lowHIntegrand Z m γ) (Ioc (0 : ℝ) 1) :=
    (complete_zero_fullLine_integrable_and_moment Z m γ hmpos).1.integrableOn
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖lowHIntegrand Z m γ y‖ ≤ 144 * D γ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hi := (extension_inner_integrable_and_bound Z y 3 (by norm_num)
      (fun n h hh => extension_positive_exp_le Z n h y hh hy)).2
    rw [lowHIntegrand, norm_mul]
    calc
      _ ≤ (6 * D γ ^ 2) * (8 * 3) :=
        mul_le_mul (extension_positive_physical_le m γ y hm hγ hy) hi
          (norm_nonneg _) (by positivity)
      _ = 144 * D γ ^ 2 := by ring
  calc
    ‖positiveExtension Z m γ‖ =
        ‖∫ y in Ioc (0 : ℝ) 1, lowHIntegrand Z m γ y‖ := by
      rw [positiveExtension, norm_neg]
    _ ≤ ∫ y in Ioc (0 : ℝ) 1, ‖lowHIntegrand Z m γ y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _y in Ioc (0 : ℝ) 1, 144 * D γ ^ 2 :=
      integral_mono_ae hf.norm (integrable_const _) hbound
    _ = 144 * D γ ^ 2 := by simp
    _ ≤ 2400 * m * D γ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- Density transport of actual finite moments.  This follows the same
withDensity API as checked4328, now in ℝ. -/
private theorem extension_central_density_integrable
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ) :
    Integrable (fun y : ℝ => ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ n) := by
  have hLp : MemLp (fun y : ℝ => y - μ) n (ProbabilityTheory.gaussianReal μ v) := by
    simpa only [Pi.sub_def, id_eq, ENNReal.coe_natCast] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := μ) (v := v) (n : ℝ≥0)).sub
        (memLp_const μ)
  have hpow : Integrable (fun y : ℝ => (y - μ) ^ n)
      (ProbabilityTheory.gaussianReal μ v) := by
    apply hLp.integrable_norm_pow'.mono' (hLp.aestronglyMeasurable.pow n)
    exact ae_of_all _ fun y => (norm_pow (y - μ) n).le
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv] at hpow
  have htransport := (integrable_withDensity_iff_integrable_smul'
    (ProbabilityTheory.measurable_gaussianPDF μ v)
    (ae_of_all volume fun _ => ProbabilityTheory.gaussianPDF_lt_top)).mp hpow
  simpa only [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul] using htransport

/-- The project supplier already contains the scalar even-moment proof and
its RemyDegenne/brownian-motion attribution.  Only n=1 and n=2 are used here. -/
private theorem extension_central_density_moments
    (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ 2) = (v : ℝ) ∧
    (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal μ v y * (y - μ) ^ 4) = 3 * (v : ℝ) ^ 2 := by
  have hs : (NNReal.sqrt v : ℝ) ^ 2 = (v : ℝ) := by
    exact_mod_cast NNReal.sq_sqrt v
  have hs4 : (NNReal.sqrt v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    calc
      _ = ((NNReal.sqrt v : ℝ) ^ 2) ^ 2 := by ring
      _ = (v : ℝ) ^ 2 := by rw [hs]
  have h2 := D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    μ (NNReal.sqrt v) 1
  have h4 := D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    μ (NNReal.sqrt v) 2
  have h2' : (∫ y : ℝ, (y - μ) ^ 2 ∂ProbabilityTheory.gaussianReal μ v) = (v : ℝ) := by
    simpa only [ProbabilityTheory.centralMoment, id_eq,
      ProbabilityTheory.integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
      show (2 * 1 : ℕ) = 2 by rfl, show (2 * 1 - 1 : ℕ) = 1 by rfl,
      NNReal.sq_sqrt, show Nat.doubleFactorial 1 = 1 by decide,
      Nat.cast_one, mul_one, hs] using h2
  have h4' : (∫ y : ℝ, (y - μ) ^ 4 ∂ProbabilityTheory.gaussianReal μ v) =
      3 * (v : ℝ) ^ 2 := by
    simpa only [ProbabilityTheory.centralMoment, id_eq,
      ProbabilityTheory.integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
      show (2 * 2 : ℕ) = 4 by rfl, show (2 * 2 - 1 : ℕ) = 3 by rfl,
      NNReal.sq_sqrt, show Nat.doubleFactorial 3 = 3 by decide,
      Nat.cast_ofNat, hs4, mul_comm] using h4
  constructor
  · rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h2'
    simpa only [smul_eq_mul] using h2'
  · rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h4'
    simpa only [smul_eq_mul] using h4'

private theorem extension_negative_tilt (m y : ℝ) (hm : 0 < m) :
    gaussianDensity m y * Real.exp (-2 * y) =
      Real.exp (-28 * m) * ProbabilityTheory.gaussianPDFReal (12 * m)
        (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hm) y := by
  have he : -(y - 16 * m) ^ 2 / (4 * m) + -2 * y =
      -28 * m + -(y - 12 * m) ^ 2 / (4 * m) := by
    field_simp [hm.ne'] <;> ring
  change (Real.exp (-(y - 16 * m) ^ 2 / (4 * m)) /
      Real.sqrt (4 * Real.pi * m)) * Real.exp (-2 * y) =
    Real.exp (-28 * m) * ((Real.sqrt (2 * Real.pi * (2 * m)))⁻¹ *
      Real.exp (-(y - 12 * m) ^ 2 / (2 * (2 * m))))
  rw [show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  calc
    _ = Real.exp (-(y - 16 * m) ^ 2 / (4 * m) + -2 * y) /
        Real.sqrt (4 * Real.pi * m) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

private theorem extension_negative_polynomial_le
    (m γ y : ℝ) (hm : 1 ≤ m) :
    |y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) ≤
      (13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9) := by
  have hmpos : 0 < m := by linarith
  have habs : |y - 12 * m| ≤ m + (y - 12 * m) ^ 2 / (4 * m) := by
    have hh : |y - 12 * m| - m ≤ (y - 12 * m) ^ 2 / (4 * m) := by
      apply (le_div_iff₀ (show 0 < 4 * m by positivity)).2
      nlinarith [sq_nonneg (|y - 12 * m| - 2 * m), sq_abs (y - 12 * m)]
    linarith
  have hfirst : |y + 1| ≤ 13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m) := by
    calc
      |y + 1| = |(y - 12 * m) + (12 * m + 1)| := by congr 1 <;> ring
      _ ≤ |y - 12 * m| + |12 * m + 1| := abs_add_le _ _
      _ = |y - 12 * m| + (12 * m + 1) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 12 * m + 1)]
      _ ≤ _ := by linarith
  have hcoord : gaussianCoordinate m y = (y - 12 * m) / (2 * m) - 2 := by
    unfold gaussianCoordinate centre
    field_simp [hmpos.ne'] <;> ring
  have hsecond : gaussianCoordinate m y ^ 2 + γ ^ 2 + 1 ≤
      (y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9 := by
    have hsq : ((y - 12 * m) / (2 * m) - 2) ^ 2 ≤
        2 * ((y - 12 * m) / (2 * m)) ^ 2 + 8 := by
      nlinarith [sq_nonneg ((y - 12 * m) / (2 * m) + 2)]
    have heq : 2 * ((y - 12 * m) / (2 * m)) ^ 2 =
        (y - 12 * m) ^ 2 / (2 * m ^ 2) := by
      field_simp [hmpos.ne'] <;> ring
    rw [hcoord]
    rw [heq] at hsq
    linarith
  exact mul_le_mul hfirst hsecond (by positivity) (by positivity)

/-- Genuine density integrability and evaluation of the polynomial majorant.
The variance is 2m, so the existing moments give 2m and 12m². -/
private theorem extension_negative_majorant_integral
    (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    let hmpos : 0 < m := by linarith
    let v := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos
    let F := fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))
    Integrable F ∧ (∫ y : ℝ, F y) ≤ 16 * m * D γ ^ 2 := by
  dsimp only
  let hmpos : 0 < m := by linarith
  let v := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos
  have hv : v ≠ 0 := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance_ne_zero m hmpos
  have hvcoe : (v : ℝ) = 2 * m := rfl
  let A : ℝ := 13 * m + 1
  let B : ℝ := γ ^ 2 + 9
  let C : ℝ := A / (2 * m ^ 2) + B / (4 * m)
  let E : ℝ := 1 / (8 * m ^ 3)
  have hi0 := ProbabilityTheory.integrable_gaussianPDFReal (12 * m) v
  have hi2 := extension_central_density_integrable (12 * m) v hv 2
  have hi4 := extension_central_density_integrable (12 * m) v hv 4
  have hmom := extension_central_density_moments (12 * m) v hv
  have hfun : (fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))) =
      (fun y : ℝ => (A * B) * ProbabilityTheory.gaussianPDFReal (12 * m) v y +
        C * (ProbabilityTheory.gaussianPDFReal (12 * m) v y * (y - 12 * m) ^ 2) +
        E * (ProbabilityTheory.gaussianPDFReal (12 * m) v y * (y - 12 * m) ^ 4)) := by
    funext y
    dsimp [A, B, C, E]
    field_simp [hmpos.ne'] <;> ring
  have hi := ((hi0.const_mul (A * B)).add (hi2.const_mul C)).add (hi4.const_mul E)
  refine ⟨?_, ?_⟩
  · change Integrable (fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9)))
    rw [hfun]
    exact hi
  have heval : (∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (12 * m) v y *
      ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))) =
      (13 * m + 3 / 2) * (γ ^ 2 + 9) + 13 + 5 / (2 * m) := by
    have hsplit := integral_add ((hi0.const_mul (A * B)).add (hi2.const_mul C))
      (hi4.const_mul E)
    have hsplit2 := integral_add (hi0.const_mul (A * B)) (hi2.const_mul C)
    simp only [Pi.add_apply] at hsplit hsplit2
    rw [hfun, hsplit, hsplit2]
    simp only [integral_const_mul, ProbabilityTheory.integral_gaussianPDFReal_eq_one _ hv,
      hmom.1, hmom.2, hvcoe]
    dsimp [A, B, C, E]
    field_simp [hmpos.ne'] <;> ring
  rw [heval]
  have hfrac : 5 / (2 * m) ≤ (5 / 2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2 * m by positivity)).2
    linarith
  have hfirst : (13 * m + 3 / 2) * (γ ^ 2 + 9) ≤
      ((29 / 2 : ℝ) * m) * (γ ^ 2 + 9) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hscalar : (29 / 2 : ℝ) * γ ^ 2 + 146 ≤ 16 * D γ ^ 2 := by
    unfold D
    nlinarith [sq_nonneg γ]
  calc
    (13 * m + 3 / 2) * (γ ^ 2 + 9) + 13 + 5 / (2 * m) ≤
        ((29 / 2 : ℝ) * m) * (γ ^ 2 + 9) + (31 / 2 : ℝ) * m := by
      linarith
    _ = m * ((29 / 2 : ℝ) * γ ^ 2 + 146) := by ring
    _ ≤ m * (16 * D γ ^ 2) := mul_le_mul_of_nonneg_left hscalar hmpos.le
    _ = 16 * m * D γ ^ 2 := by ring

private theorem extension_negative_pointwise
    (Z : CompleteZeroFamily) (m γ y : ℝ) (hm : 1 ≤ m) (hy : y < 0) :
    let hmpos : 0 < m := by linarith
    ‖lowHIntegrand Z m γ y‖ ≤
      (24 * Real.exp (-28 * m)) *
        (ProbabilityTheory.gaussianPDFReal (12 * m)
          (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos) y *
          ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
            ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))) := by
  dsimp only
  have hmpos : 0 < m := by linarith
  have hi := (extension_inner_integrable_and_bound Z y (Real.exp (-2 * y))
    (Real.exp_nonneg _) (fun n h hh => extension_negative_exp_le Z n h y hh hy.le)).2
  have hp := extension_negative_polynomial_le m γ y hm
  have hd := extension_density_nonneg m y hmpos
  rw [lowHIntegrand, norm_mul, extension_physical_norm m γ y hmpos]
  calc
    _ ≤ (3 * |y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1) *
        gaussianDensity m y) * (8 * Real.exp (-2 * y)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 24 * (|y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1)) *
        (gaussianDensity m y * Real.exp (-2 * y)) := by ring
    _ = 24 * (|y + 1| * (gaussianCoordinate m y ^ 2 + γ ^ 2 + 1)) *
        (Real.exp (-28 * m) * ProbabilityTheory.gaussianPDFReal (12 * m)
          (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos) y) := by
      rw [extension_negative_tilt m y hmpos]
    _ ≤ 24 * ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
        ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9)) *
        (Real.exp (-28 * m) * ProbabilityTheory.gaussianPDFReal (12 * m)
          (D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos) y) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_nonneg (Real.exp_nonneg _) (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))
    _ = _ := by ring

theorem complete_zero_negative_extension_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖negativeExtension Z m γ‖ ≤ 384 * m * D γ ^ 2 * Real.exp (-28 * m) := by
  let hmpos : 0 < m := by linarith
  let v := D5.S3.Arith.Robin.CompleteLowHGaussianMoment.variance m hmpos
  let F := fun y : ℝ => ProbabilityTheory.gaussianPDFReal (12 * m) v y *
    ((13 * m + 1 + (y - 12 * m) ^ 2 / (4 * m)) *
      ((y - 12 * m) ^ 2 / (2 * m ^ 2) + γ ^ 2 + 9))
  have hF : Integrable F ∧ (∫ y : ℝ, F y) ≤ 16 * m * D γ ^ 2 :=
    extension_negative_majorant_integral m γ hm hγ
  have hFnonneg : ∀ y, 0 ≤ F y := by
    intro y
    dsimp [F]
    exact mul_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
      (mul_nonneg (by positivity) (by positivity))
  have hG : Integrable (fun y => (24 * Real.exp (-28 * m)) * F y) :=
    hF.1.const_mul _
  have hf : IntegrableOn (lowHIntegrand Z m γ) (Iio (0 : ℝ)) :=
    (complete_zero_fullLine_integrable_and_moment Z m γ hmpos).1.integrableOn
  have hbound : ∀ᵐ y ∂(volume.restrict (Iio (0 : ℝ))),
      ‖lowHIntegrand Z m γ y‖ ≤ (24 * Real.exp (-28 * m)) * F y := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    exact extension_negative_pointwise Z m γ y hm hy
  calc
    ‖negativeExtension Z m γ‖ = ‖∫ y in Iio (0 : ℝ), lowHIntegrand Z m γ y‖ := by
      rw [negativeExtension, norm_neg]
    _ ≤ ∫ y in Iio (0 : ℝ), ‖lowHIntegrand Z m γ y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Iio (0 : ℝ), (24 * Real.exp (-28 * m)) * F y :=
      integral_mono_ae hf.norm hG.integrableOn hbound
    _ ≤ ∫ y : ℝ, (24 * Real.exp (-28 * m)) * F y :=
      setIntegral_le_integral hG (ae_of_all volume fun y =>
        mul_nonneg (by positivity) (hFnonneg y))
    _ = (24 * Real.exp (-28 * m)) * (∫ y : ℝ, F y) := integral_const_mul _ _
    _ ≤ (24 * Real.exp (-28 * m)) * (16 * m * D γ ^ 2) :=
      mul_le_mul_of_nonneg_left hF.2 (by positivity)
    _ = 384 * m * D γ ^ 2 * Real.exp (-28 * m) := by ring


structure LowHCertificates (Z : CompleteZeroFamily) (m γ : ℝ) : Prop where
  m_ge_one : 1 ≤ m
  gamma_gt_ten : 10 < γ

lemma shell_exp_constant240 (m γ : ℝ) :
    240 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) =
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
  have he : -100 * m + 17 * m = -83 * m := by ring
  calc
    240 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) =
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
        calc
          _ = (m * D γ ^ 2 * 2400000) *
              (Real.exp (-100 * m) * Real.exp (17 * m)) := by ring
          _ = _ := by rw [← Real.exp_add, he]; ring

/-- All-index complex shell consumer, with the original numerical coefficient
    and decay exponent.  Fubini and extension assumptions are not needed. -/
theorem complete_real_line_mean_bound
    (Z : CompleteZeroFamily) (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖completeRealLineMean Z m γ‖ ≤
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := by
  have hm0 : 0 ≤ m := by linarith
  have hcount := (shell_summable_and_count_bound Z m hm).2
  calc
    _ ≤ 240 * m * D γ ^ 2 * shellSum Z m * Real.exp (17 * m) :=
      complete_real_line_mean_bound240 Z m γ hm hγ
    _ ≤ 240 * m * D γ ^ 2 * (10000 * Real.exp (-100 * m)) *
        Real.exp (17 * m) := by
      gcongr <;> exact hcount
    _ = m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) := shell_exp_constant240 m γ

theorem complete_low_h_weighted_mean_bound
    (Z : CompleteZeroFamily) (m γ : ℝ)
    (h : LowHCertificates Z m γ) :
    IntegrableOn (lowHIntegrand Z m γ) (Ioi (1 : ℝ)) ∧
      ‖lowHMean Z m γ‖ ≤
        m * D γ ^ 2 *
          (2400000 * Real.exp (-83 * m) + 2400 +
            384 * Real.exp (-28 * m)) := by
  have hm : 0 < m := by linarith [h.m_ge_one]
  refine ⟨complete_zero_lowH_integrable Z m γ hm, ?_⟩
  rw [complete_zero_fubini_exchange Z m γ hm]
  have hshell : ‖completeRealLineMean Z m γ‖ ≤
      m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) :=
    complete_real_line_mean_bound Z m γ h.m_ge_one h.gamma_gt_ten
  calc
    ‖completeRealLineMean Z m γ + positiveExtension Z m γ +
        negativeExtension Z m γ‖ ≤
        ‖completeRealLineMean Z m γ‖ +
          ‖positiveExtension Z m γ‖ + ‖negativeExtension Z m γ‖ := by
      exact norm_add₃_le
    _ ≤ m * D γ ^ 2 * (2400000 * Real.exp (-83 * m)) +
        2400 * m * D γ ^ 2 +
        384 * m * D γ ^ 2 * Real.exp (-28 * m) := by
      linarith [hshell,
        complete_zero_positive_extension_bound Z m γ h.m_ge_one h.gamma_gt_ten,
        complete_zero_negative_extension_bound Z m γ h.m_ge_one h.gamma_gt_ten]
    _ = m * D γ ^ 2 *
        (2400000 * Real.exp (-83 * m) + 2400 +
          384 * Real.exp (-28 * m)) := by ring

/- At compilation this inspection reads the original named proof terms. -/
run_cmd do
  let env ← Lean.getEnv
  for name in [``extension_kernel_norm_le,
      ``extension_inner_integrable_and_bound,
      ``extension_positive_exp_le,
      ``extension_negative_exp_le,
      ``extension_density_nonneg,
      ``extension_physical_norm,
      ``extension_positive_physical_le,
      ``complete_zero_positive_extension_bound,
      ``extension_central_density_integrable,
      ``extension_central_density_moments,
      ``extension_negative_tilt,
      ``extension_negative_polynomial_le,
      ``extension_negative_majorant_integral,
      ``extension_negative_pointwise,
      ``complete_zero_negative_extension_bound,
      ``divided_cubic_polynomial_bound_two,
      ``divided_cubic_coefficient_core_two,
      ``shell_term_bound24,
      ``shell_terms_norm_summable,
      ``divided_cubic_coefficient_core_bound,
      ``shell_term_bound240,
      ``complete_real_line_mean_bound240,
      ``complete_real_line_mean_bound,
      ``complete_low_h_weighted_mean_bound] do
    let some info := env.find? name | throwError "missing native consumer {name}"
    let some value := info.value? (allowOpaque := true) |
      throwError "missing native proof {name}"
    let refs := value.getUsedConstants.filter fun n =>
      n.toString.startsWith "D5." || n.toString.startsWith "_private.D5."
    Lean.logInfo m!"RH_EXTENSION_NATIVE_CONSUMER {name}: {refs}"


end D5.S3.Arith.Robin.CompleteLowHWeightedSpectralMean
