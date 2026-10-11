/- GID: D5/S3/Arith/Robin/CompleteCoefficientLaplace
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/CompleteCoefficientLaplace
   mirror-E: none(waiver:analytic-integral-identity)
   anchors: []
   utility: none
   digest: The literal complete Robin coefficient has an absolutely convergent Laplace resolvent and a factor-one modulus bound. -/

import D5.S3.Analytic.LiCausalTrichotomy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/- SOURCE ONLY / UNCOMPILED: every declaration in this module, including private
helpers, awaits the caller's scoped build and axiom-closure checks. No statement
here is a Lean acceptance receipt. The original source is literal M1 in
Library/ArithSums/nicolas2025comparison.md at
7f52221f2e23da81475058d5b5b6620e68709401. -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace D5.S3.Arith.Robin.CompleteCoefficientLaplace

open D5.S3.Analytic.LiCausalTrichotomy
  (integrableOn_complex_laplace_moment integral_complex_laplace_moment)

/-- Literal M1 integrand. On its integration domain `u > A > 1`, `cpow`
uses the real logarithm of the positive real base. -/
noncomputable def physicalIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (s - 2) * (((1 + Real.log u) / (Real.log u) ^ 2 : ℝ) : ℂ)

/-- The physical coefficient, defined by the original integral, not the resolvent. -/
noncomputable def coefficient (A : ℝ) (s : ℂ) : ℂ :=
  s⁻¹ * ∫ u in Ioi A, physicalIntegrand s u

/-- The logarithmic weight of the complete coefficient. -/
noncomputable def logWeight (x : ℝ) : ℝ := x⁻¹ + x⁻¹ ^ 2

noncomputable def logIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((s - 1) * (x : ℂ)) * (logWeight x : ℂ)

/-- The positive numerator, with its full linear term. -/
noncomputable def numerator (L t : ℝ) : ℝ := (1 + t) * Real.exp (-L * t)

/-- The actual kernel whose product integrability is established before Fubini. -/
noncomputable def kernel (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (1 + (p.2 : ℂ)) * Complex.exp (-((1 - s) + (p.2 : ℂ)) * (p.1 : ℂ))

noncomputable def resolventIntegrand (L : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  (numerator L t : ℂ) / ((1 - s) + (t : ℂ))

private lemma logWeight_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ logWeight x := by
  unfold logWeight
  positivity

private lemma logWeight_antitone {L x : ℝ} (hL : 0 < L) (hx : L ≤ x) :
    logWeight x ≤ logWeight L := by
  have hi : x⁻¹ ≤ L⁻¹ := inv_anti₀ hL hx
  have hx0 : 0 < x := hL.trans_le hx
  unfold logWeight
  have hix : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hiL : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hsq : x⁻¹ ^ 2 ≤ L⁻¹ ^ 2 := (sq_le_sq₀ hix hiL).mpr hi
  linarith

private lemma numerator_nonneg (L : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ numerator L t := by
  unfold numerator
  positivity

private lemma numerator_coe (L t : ℝ) :
    (numerator L t : ℂ) = (1 + (t : ℂ)) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
  simp only [numerator, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg]

private lemma numerator_complex_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun t : ℝ => (numerator L t : ℂ)) (Ioi 0) := by
  have ha : (-(L : ℂ)).re < 0 := by simpa using (neg_lt_zero.mpr hL)
  have h0 := integrableOn_complex_laplace_moment ha 0
  have h1 := integrableOn_complex_laplace_moment ha 1
  apply (h0.add h1).congr
  filter_upwards [] with t
  rw [numerator_coe]
  simp only [Pi.add_apply, pow_zero, pow_one, one_mul]
  ring

private lemma numerator_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (numerator L) (Ioi 0) := by
  simpa only [Complex.ofReal_re] using (numerator_complex_integrable hL).re

private lemma numerator_complex_integral {L : ℝ} (hL : 0 < L) :
    (∫ t in Ioi (0 : ℝ), (numerator L t : ℂ)) = (logWeight L : ℂ) := by
  have ha : (-(L : ℂ)).re < 0 := by simpa using (neg_lt_zero.mpr hL)
  have h0 := integrableOn_complex_laplace_moment ha 0
  have h1 := integrableOn_complex_laplace_moment ha 1
  calc
    _ = (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 0 * Complex.exp (-(L : ℂ) * t)) +
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 1 * Complex.exp (-(L : ℂ) * t) := by
      rw [← integral_add h0 h1]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      rw [numerator_coe]
      simp only [pow_zero, pow_one, one_mul]
      ring
    _ = (logWeight L : ℂ) := by
      rw [integral_complex_laplace_moment ha 0,
        integral_complex_laplace_moment ha 1]
      simp only [logWeight, Complex.ofReal_add, Complex.ofReal_inv,
        Complex.ofReal_pow]
      norm_num <;> field_simp [Complex.ofReal_ne_zero.mpr hL.ne'] <;> ring

private lemma numerator_integral {L : ℝ} (hL : 0 < L) :
    (∫ t in Ioi (0 : ℝ), numerator L t) = logWeight L := by
  apply Complex.ofReal_injective
  rw [← integral_ofReal]
  exact numerator_complex_integral hL

private lemma logIntegrand_integrable {L : ℝ} {s : ℂ}
    (hL : 0 < L) (hs : s.re < 1) : IntegrableOn (logIntegrand s) (Ioi L) := by
  have he := integrableOn_exp_mul_Ioi (a := s.re - 1) (by linarith) L
  apply (he.const_mul (logWeight L)).mono'
  · have hm : Measurable (logIntegrand s) := by
      unfold logIntegrand logWeight
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hL.trans hx
    simp only [logIntegrand, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (logWeight_nonneg hx0), Complex.mul_re,
      Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact (mul_le_mul_of_nonneg_left (logWeight_antitone hL hx.le)
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)

private lemma physical_exp_jacobian (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Real.exp x • physicalIntegrand s (Real.exp x) = logIntegrand s x := by
  have he0 : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
  rw [physicalIntegrand, Complex.real_smul, Complex.cpow_def_of_ne_zero he0,
    ← Complex.ofReal_log (Real.exp_pos x).le, logIntegrand]
  simp only [Real.log_exp]
  have hw : (((1 + x) / x ^ 2 : ℝ) : ℂ) = (logWeight x : ℂ) := by
    congr 1
    unfold logWeight
    field_simp [hx.ne']
    <;> ring
  rw [hw, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private lemma physical_integrable {A : ℝ} {s : ℂ} (hA : 1 < A) (hs : s.re < 1) :
    IntegrableOn (physicalIntegrand s) (Ioi A) := by
  have hL : 0 < Real.log A := Real.log_pos hA
  have hj : IntegrableOn
      (fun x => Real.exp x • physicalIntegrand s (Real.exp x)) (Ioi (Real.log A)) := by
    apply (logIntegrand_integrable hL hs).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact (physical_exp_jacobian s (hL.trans hx)).symm
  have h := (integrableOn_comp_exp_Ioi (physicalIntegrand s) (Real.log A)).mp hj
  simpa only [Real.exp_log (show 0 < A by linarith)] using h

private lemma coefficient_log_substitution {A : ℝ} (hA : 1 < A) (s : ℂ) :
    coefficient A s = s⁻¹ * ∫ x in Ioi (Real.log A), logIntegrand s x := by
  have hL : 0 < Real.log A := Real.log_pos hA
  have h := integral_comp_exp_Ioi (physicalIntegrand s) (Real.log A)
  rw [Real.exp_log (show 0 < A by linarith)] at h
  unfold coefficient
  rw [← h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact physical_exp_jacobian s (hL.trans hx)

private lemma kernel_norm (s : ℂ) {x t : ℝ} (ht : 0 ≤ t) :
    ‖kernel s (x, t)‖ = (1 + t) * Real.exp (-((1 - s.re) + t) * x) := by
  have hr : (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) := by push_cast; rfl
  rw [kernel, norm_mul, hr, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1 + t), Complex.norm_exp]
  simp only [Complex.add_re,
    Complex.one_re, Complex.ofReal_re, Complex.add_im, Complex.one_im,
    Complex.ofReal_im, add_zero, zero_add, Complex.neg_re, Complex.mul_re, Complex.neg_im,
    Complex.sub_re, mul_zero, sub_zero]

private lemma kernel_norm_majorant (s : ℂ) {L x t : ℝ}
    (hx : L ≤ x) (ht : 0 ≤ t) :
    ‖kernel s (x, t)‖ ≤ Real.exp ((s.re - 1) * x) * numerator L t := by
  rw [kernel_norm s ht]
  have he : -((1 - s.re) + t) * x ≤ (s.re - 1) * x + (-L * t) := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hx)]
  calc
    _ ≤ (1 + t) * Real.exp ((s.re - 1) * x + (-L * t)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by linarith)
    _ = _ := by rw [Real.exp_add]; unfold numerator; ring

private lemma kernel_integrable {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : s.re < 1) :
    Integrable (kernel s)
      ((volume.restrict (Ioi L)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have he := integrableOn_exp_mul_Ioi (a := s.re - 1) (by linarith) L
  have hmajor := he.mul_prod (numerator_integrable hL)
  apply hmajor.mono'
  · have hc : Continuous (kernel s) := by unfold kernel; fun_prop
    exact hc.aestronglyMeasurable
  · have hdom : ∀ᵐ p : ℝ × ℝ ∂
        ((volume.restrict (Ioi L)).prod (volume.restrict (Ioi (0 : ℝ)))),
        p ∈ Ioi L ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact self_mem_ae_restrict (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hdom] with p hp
    exact kernel_norm_majorant s hp.1.le hp.2.le

private lemma kernel_as_numerator (s : ℂ) (x t : ℝ) :
    kernel s (x, t) = Complex.exp ((s - 1) * (x : ℂ)) * (numerator x t : ℂ) := by
  rw [numerator_coe]
  calc
    _ = (1 + (t : ℂ)) *
        (Complex.exp ((s - 1) * (x : ℂ)) * Complex.exp (-(x : ℂ) * (t : ℂ))) := by
      rw [← Complex.exp_add]
      unfold kernel
      congr 2
      ring
    _ = _ := by ring

private lemma kernel_integral_t (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), kernel s (x, t)) = logIntegrand s x := by
  simp_rw [kernel_as_numerator]
  rw [integral_const_mul, numerator_complex_integral hx]

private lemma denominator_norm {s : ℂ} (hs : s.re < 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖1 - s‖ ≤ ‖(1 - s) + (t : ℂ)‖ := by
  have hp : 0 ≤ (1 - s.re) * t := mul_nonneg (by linarith) ht
  have hsq : ‖1 - s‖ ^ 2 ≤ ‖(1 - s) + (t : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private lemma one_sub_ne_zero {s : ℂ} (hs : s.re < 1) : 1 - s ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
  linarith

private lemma resolvent_norm_majorant {s : ℂ} (hs : s.re < 1) (L : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖resolventIntegrand L s t‖ ≤ numerator L t / ‖1 - s‖ := by
  rw [resolventIntegrand, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (numerator_nonneg L ht)]
  exact div_le_div_of_nonneg_left (numerator_nonneg L ht)
    (norm_pos_iff.mpr (one_sub_ne_zero hs)) (denominator_norm hs ht)

private lemma resolvent_integrable {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : s.re < 1) :
    IntegrableOn (resolventIntegrand L s) (Ioi (0 : ℝ)) := by
  apply ((numerator_integrable hL).div_const ‖1 - s‖).mono'
  · have hm : Measurable (resolventIntegrand L s) := by
      unfold resolventIntegrand numerator
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact resolvent_norm_majorant hs L ht.le

private lemma kernel_integral_x {s : ℂ} (hs : s.re < 1) (L : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioi L, kernel s (x, t)) =
      Complex.exp ((s - 1) * (L : ℂ)) * resolventIntegrand L s t := by
  have ha : (-((1 - s) + (t : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.sub_re,
      Complex.one_re, Complex.ofReal_re]
    linarith
  have he : Complex.exp (-((1 - s) + (t : ℂ)) * (L : ℂ)) =
      Complex.exp ((s - 1) * (L : ℂ)) * (Real.exp (-L * t) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [kernel]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi ha L, neg_div_neg_eq, he]
  unfold resolventIntegrand numerator
  push_cast
  ring

private lemma log_integral_resolvent {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : s.re < 1) :
    (∫ x in Ioi L, logIntegrand s x) =
      Complex.exp ((s - 1) * (L : ℂ)) *
        ∫ t in Ioi (0 : ℝ), resolventIntegrand L s t := by
  calc
    _ = ∫ x in Ioi L, ∫ t in Ioi (0 : ℝ), kernel s (x, t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (kernel_integral_t s (hL.trans hx)).symm
    _ = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi L, kernel s (x, t) :=
      integral_integral_swap (kernel_integrable hL hs)
    _ = ∫ t in Ioi (0 : ℝ),
        Complex.exp ((s - 1) * (L : ℂ)) * resolventIntegrand L s t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact kernel_integral_x hs L ht.le
    _ = _ := integral_const_mul _ _

private lemma coefficient_resolvent {A : ℝ} {s : ℂ} (hA : 1 < A) (hs : s.re < 1) :
    coefficient A s = (A : ℂ) ^ (s - 1) / s *
      ∫ t in Ioi (0 : ℝ), resolventIntegrand (Real.log A) s t := by
  have hA0 : 0 < A := by linarith
  have hp : (A : ℂ) ^ (s - 1) = Complex.exp ((s - 1) * (Real.log A : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA0.ne'),
      ← Complex.ofReal_log hA0.le]
    congr 1
    ring
  rw [coefficient_log_substitution hA s, log_integral_resolvent (Real.log_pos hA) hs,
    ← hp]
  ring

private lemma resolvent_integral_norm {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : s.re < 1) :
    ‖∫ t in Ioi (0 : ℝ), resolventIntegrand L s t‖ ≤ logWeight L / ‖1 - s‖ := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖resolventIntegrand L s t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), numerator L t / ‖1 - s‖ := by
      apply setIntegral_mono_on (resolvent_integrable hL hs).norm
        ((numerator_integrable hL).div_const ‖1 - s‖) measurableSet_Ioi
      intro t ht
      exact resolvent_norm_majorant hs L ht.le
    _ = _ := by rw [integral_div, numerator_integral hL]

/-- Complete coefficient theorem: literal physical integrability, exact logarithmic
substitution, actual restricted-product integrability, resolvent integrability, full
complex identity and factor-one norm estimate, for every `A > 1` and every point
of the open strip. No finite endpoint or signed zero-series assertion is included.
SOURCE ONLY / UNCOMPILED. -/
theorem complete_coefficient_laplace {A : ℝ} {s : ℂ}
    (hA : 1 < A) (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    IntegrableOn (physicalIntegrand s) (Ioi A) ∧
    coefficient A s = s⁻¹ * (∫ x in Ioi (Real.log A), logIntegrand s x) ∧
    Integrable (kernel s)
      ((volume.restrict (Ioi (Real.log A))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    IntegrableOn (resolventIntegrand (Real.log A) s) (Ioi (0 : ℝ)) ∧
    coefficient A s = (A : ℂ) ^ (s - 1) / s *
      (∫ t in Ioi (0 : ℝ), resolventIntegrand (Real.log A) s t) ∧
    ‖coefficient A s‖ ≤
      A ^ (s.re - 1) * logWeight (Real.log A) / (‖s‖ * ‖1 - s‖) := by
  have hL : 0 < Real.log A := Real.log_pos hA
  refine ⟨physical_integrable hA hσ1, coefficient_log_substitution hA s,
    kernel_integrable hL hσ1, resolvent_integrable hL hσ1,
    coefficient_resolvent hA hσ1, ?_⟩
  have hA0 : 0 < A := by linarith
  have hs0 : s ≠ 0 := by intro h; simp [h] at hσ0
  have hn := resolvent_integral_norm hL hσ1
  rw [coefficient_resolvent hA hσ1, norm_mul, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hA0]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ A ^ (s.re - 1) / ‖s‖ * (logWeight (Real.log A) / ‖1 - s‖) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by
      field_simp [norm_ne_zero_iff.mpr hs0, norm_ne_zero_iff.mpr (one_sub_ne_zero hσ1)]
      <;> ring

end D5.S3.Arith.Robin.CompleteCoefficientLaplace
