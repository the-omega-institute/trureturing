/- GID: D5/S3/Divergence/CauchyMeasureEntropy
   generality: G
   mirror-B: D5/B/S3/Divergence/CauchyMeasureEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluate Cauchy measure relative entropy and prove its scale-flow laws. -/

/- Library search: the pinned Mathlib Cauchy and KL APIs supply density normalization
and Radon--Nikodym calculus, but not this logarithmic expectation. The frozen
CauchyClosedForm owner supplies the scalar expression and its shifted-scale identity.
The new analytic step differentiates a logarithmic expectation under an integral,
using a uniform bound and a mixed rational-kernel calculation. -/

import D5.S3.Divergence.CauchyClosedForm
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace D5.S3.Divergence.CauchyMeasureEntropy

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open D5.S3.Divergence.CauchyClosedForm

private lemma cauchy_ac (gamma : ℝ) (a b : ℝ≥0) (ha : a ≠ 0) (hb : b ≠ 0) :
    cauchyMeasure gamma a ≪ cauchyMeasure gamma b := by
  rw [cauchyMeasure_of_scale_ne_zero gamma ha, cauchyMeasure_of_scale_ne_zero gamma hb]
  exact (withDensity_absolutelyContinuous _ _).trans
    (withDensity_absolutelyContinuous'
      (measurable_cauchyPDF gamma b).aemeasurable
      (Filter.Eventually.of_forall fun x =>
        (ENNReal.ofReal_pos.mpr (cauchyPDF_pos gamma hb x)).ne'))

private lemma cauchy_llr (gamma : ℝ) (a b : ℝ≥0) (ha : a ≠ 0) (hb : b ≠ 0) :
    llr (cauchyMeasure gamma a) (cauchyMeasure gamma b) =ᵐ[cauchyMeasure gamma a]
      fun x => Real.log (cauchyPDFReal gamma a x / cauchyPDFReal gamma b x) := by
  have hac : cauchyMeasure gamma a ≪ volume := by
    rw [cauchyMeasure_of_scale_ne_zero gamma ha]
    exact withDensity_absolutelyContinuous _ _
  have hright := Measure.rnDeriv_withDensity_right
    (cauchyMeasure gamma a) volume (measurable_cauchyPDF gamma b).aemeasurable
    (Filter.Eventually.of_forall fun x =>
      (ENNReal.ofReal_pos.mpr (cauchyPDF_pos gamma hb x)).ne')
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_top)
  have hleft : (cauchyMeasure gamma a).rnDeriv volume =ᵐ[volume] cauchyPDF gamma a := by
    rw [cauchyMeasure_of_scale_ne_zero gamma ha]
    exact Measure.rnDeriv_withDensity _ (measurable_cauchyPDF gamma a)
  rw [← cauchyMeasure_of_scale_ne_zero gamma hb] at hright
  filter_upwards [hac.ae_le hright, hac.ae_le hleft] with x hx hy
  simp only [llr, hx, hy, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [cauchyPDF, cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos gamma ha x).le,
    ENNReal.toReal_ofReal (cauchyPDF_pos gamma hb x).le]
  congr 1
  ring

private lemma cauchy_ratio_bound (gamma : ℝ) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ) :
    cauchyPDFReal gamma a x / cauchyPDFReal gamma b x ≤ (a : ℝ) / b + b / a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast pos_iff_ne_zero.mpr ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast pos_iff_ne_zero.mpr hb
  have hqa : 0 < (x - gamma) ^ 2 + (a : ℝ) ^ 2 := by positivity
  have hqb : 0 < (x - gamma) ^ 2 + (b : ℝ) ^ 2 := by positivity
  have heq : cauchyPDFReal gamma a x / cauchyPDFReal gamma b x =
      (a : ℝ) * ((x - gamma) ^ 2 + (b : ℝ) ^ 2) /
        ((b : ℝ) * ((x - gamma) ^ 2 + (a : ℝ) ^ 2)) := by
    unfold cauchyPDFReal
    field_simp
  rw [heq, div_le_iff₀ (mul_pos hb' hqa)]
  have hid : ((a : ℝ) / b + b / a) *
      ((b : ℝ) * ((x - gamma) ^ 2 + (a : ℝ) ^ 2)) -
      (a : ℝ) * ((x - gamma) ^ 2 + (b : ℝ) ^ 2) =
      (a : ℝ) ^ 3 + (b : ℝ) ^ 2 * (x - gamma) ^ 2 / a := by
    field_simp
    ring
  have hnonneg : 0 ≤ (a : ℝ) ^ 3 + (b : ℝ) ^ 2 * (x - gamma) ^ 2 / a := by positivity
  linarith

private lemma cauchy_log_integrable (gamma : ℝ) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun x => Real.log (cauchyPDFReal gamma a x / cauchyPDFReal gamma b x))
      (cauchyMeasure gamma a) := by
  refine (integrable_const ((a : ℝ) / b + b / a)).mono'
    (((measurable_cauchyPDFReal gamma a).div
      (measurable_cauchyPDFReal gamma b)).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_le]
  have hpos := div_pos (cauchyPDF_pos gamma ha x) (cauchyPDF_pos gamma hb x)
  have hupper := (Real.log_le_self hpos.le).trans (cauchy_ratio_bound gamma a b ha hb x)
  have hlower := (Real.log_le_self (inv_pos.mpr hpos).le).trans
    (show (cauchyPDFReal gamma a x / cauchyPDFReal gamma b x)⁻¹ ≤
      (a : ℝ) / b + b / a by
      simpa [inv_div, add_comm] using cauchy_ratio_bound gamma b a hb ha x)
  rw [Real.log_inv] at hlower
  exact ⟨by linarith, hupper⟩

-- Partial fractions reduce the mixed rational kernel to two normalized densities.
private lemma cauchy_kernel_integral (gamma : ℝ) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (∫ x, cauchyPDFReal gamma a x * (2 * (b : ℝ) / ((x - gamma)^2 + (b : ℝ)^2))) =
      2 / ((a : ℝ) + b) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast pos_iff_ne_zero.mpr ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast pos_iff_ne_zero.mpr hb
  have hab' : (a : ℝ) ≠ b := by exact_mod_cast hab
  have hden : (b : ℝ)^2 - (a : ℝ)^2 ≠ 0 := by
    intro h
    have heq : (b : ℝ) = a := by nlinarith
    exact hab' heq.symm
  have hshape : ∀ x : ℝ,
      cauchyPDFReal gamma a x * (2 * (b : ℝ) / ((x - gamma)^2 + (b : ℝ)^2)) =
      (2 * (b : ℝ) * cauchyPDFReal gamma a x -
        2 * (a : ℝ) * cauchyPDFReal gamma b x) / ((b : ℝ)^2 - (a : ℝ)^2) := by
    intro x
    have hqa : (x - gamma)^2 + (a : ℝ)^2 ≠ 0 := by positivity
    have hqb : (x - gamma)^2 + (b : ℝ)^2 ≠ 0 := by positivity
    unfold cauchyPDFReal
    field_simp
    ring
  simp_rw [hshape]
  rw [integral_div, integral_sub
    ((integrable_cauchyPDFReal (γ := a) gamma).const_mul _)
    ((integrable_cauchyPDFReal (γ := b) gamma).const_mul _),
    integral_const_mul, integral_const_mul, integral_cauchyPDFReal_eq_one gamma ha,
    integral_cauchyPDFReal_eq_one gamma hb]
  field_simp
  ring

private lemma cauchy_log_deriv (gamma a t x : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => Real.log a - Real.log u + Real.log ((x - gamma)^2 + u^2) -
        Real.log ((x - gamma)^2 + a^2))
      (2 * t / ((x - gamma)^2 + t^2) - t⁻¹) t := by
  have hd := ((((hasDerivAt_const t (Real.log a)).sub
    ((hasDerivAt_id t).log ht.ne')).add
    ((((hasDerivAt_id t).pow 2).const_add ((x - gamma)^2)).log (by
      dsimp
      positivity))).sub_const
      (Real.log ((x - gamma)^2 + a^2)))
  simpa [sub_eq_add_neg, add_comm] using hd

private lemma cauchy_log_deriv_bound (gamma b t x : ℝ) (hb : 0 < b) (ht : b / 2 < t) :
    |2 * t / ((x - gamma)^2 + t^2) - t⁻¹| ≤ 6 / b := by
  have ht' : 0 < t := by linarith
  have hq : 0 < (x - gamma)^2 + t^2 := by positivity
  have hratio : 2 * t / ((x - gamma)^2 + t^2) ≤ 2 / t := by
    apply (div_le_div_iff₀ hq ht').2
    nlinarith [sq_nonneg (x - gamma)]
  calc
    _ ≤ |2 * t / ((x - gamma)^2 + t^2)| + |t⁻¹| := abs_sub _ _
    _ = 2 * t / ((x - gamma)^2 + t^2) + 1 / t := by
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity), one_div]
    _ ≤ 2 / t + 1 / t := add_le_add hratio le_rfl
    _ = 3 / t := by ring
    _ ≤ 6 / b := by
      apply (div_le_div_iff₀ ht' hb).2
      linarith

private lemma cauchy_log_density (gamma : ℝ) (a : ℝ≥0) (ha : a ≠ 0) (x : ℝ) :
    Real.log (cauchyPDFReal gamma a x) =
      -Real.log Real.pi + Real.log a - Real.log ((x - gamma)^2 + (a : ℝ)^2) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hq : (x - gamma)^2 + (a : ℝ)^2 ≠ 0 := by positivity
  rw [cauchyPDFReal, Real.log_mul (mul_ne_zero (inv_ne_zero Real.pi_ne_zero) ha')
    (inv_ne_zero hq), Real.log_mul (inv_ne_zero Real.pi_ne_zero) ha']
  simp only [Real.log_inv]
  ring

private lemma cauchy_log_ratio (gamma : ℝ) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ) :
    Real.log (cauchyPDFReal gamma a x / cauchyPDFReal gamma b x) =
      Real.log a - Real.log b + Real.log ((x - gamma)^2 + (b : ℝ)^2) -
        Real.log ((x - gamma)^2 + (a : ℝ)^2) := by
  rw [Real.log_div (cauchyPDF_pos gamma ha x).ne' (cauchyPDF_pos gamma hb x).ne',
    cauchy_log_density gamma a ha, cauchy_log_density gamma b hb]
  ring

private lemma cauchy_log_expression_integrable (gamma : ℝ) (a : ℝ≥0) (ha : a ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    Integrable (fun x => Real.log a - Real.log b + Real.log ((x - gamma)^2 + b^2) -
      Real.log ((x - gamma)^2 + (a : ℝ)^2)) (cauchyMeasure gamma a) := by
  have hb' : b.toNNReal ≠ 0 := by simpa using hb
  convert cauchy_log_integrable gamma a b.toNNReal ha hb' using 1
  ext x
  rw [cauchy_log_ratio gamma a b.toNNReal ha hb', Real.coe_toNNReal b hb.le]

-- The derivative bound uses a neighborhood independent of the integration variable.
private lemma cauchy_expectation_has_deriv_at (gamma : ℝ) (a : ℝ≥0) (ha : a ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    HasDerivAt (fun u : ℝ => ∫ x,
      Real.log a - Real.log u + Real.log ((x - gamma)^2 + u^2) -
        Real.log ((x - gamma)^2 + (a : ℝ)^2) ∂cauchyMeasure gamma a)
      (∫ x, 2*b / ((x - gamma)^2 + b^2) - b⁻¹ ∂cauchyMeasure gamma a) b := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioi (b/2)) (bound := fun _ : ℝ => 6/b)
    (F' := fun u x : ℝ => 2*u / ((x - gamma)^2 + u^2) - u⁻¹)
    (Ioi_mem_nhds (by linarith)) ?_ (cauchy_log_expression_integrable gamma a ha b hb)
    ?_ ?_ (integrable_const _) ?_).2
  · exact Filter.Eventually.of_forall fun u =>
      (show Measurable (fun x => Real.log a - Real.log u +
        Real.log ((x - gamma)^2 + u^2) - Real.log ((x - gamma)^2 + (a : ℝ)^2)) by
          fun_prop).aestronglyMeasurable
  · exact (show Measurable (fun x => 2*b / ((x - gamma)^2 + b^2) - b⁻¹) by
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x t ht => by
      simpa only [Real.norm_eq_abs] using cauchy_log_deriv_bound gamma b t x hb ht
  · exact Filter.Eventually.of_forall fun x t ht =>
      cauchy_log_deriv gamma a t x (by change b/2 < t at ht; linarith)

private lemma cauchy_kernel_expectation (gamma : ℝ) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (∫ x, 2 * (b : ℝ) / ((x - gamma)^2 + (b : ℝ)^2) ∂cauchyMeasure gamma a) =
      2 / ((a : ℝ) + b) := by
  rw [cauchyMeasure_of_scale_ne_zero gamma ha,
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF gamma a)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos gamma ha _).le, smul_eq_mul]
  exact cauchy_kernel_integral gamma a b ha hb hab

private lemma cauchy_expectation_derivative (gamma : ℝ) (a : ℝ≥0) (ha : a ≠ 0)
    (b : ℝ) (hb : 0 < b) (hab : (a : ℝ) ≠ b) :
    HasDerivAt (fun u : ℝ => ∫ x,
      Real.log a - Real.log u + Real.log ((x - gamma)^2 + u^2) -
        Real.log ((x - gamma)^2 + (a : ℝ)^2) ∂cauchyMeasure gamma a)
      (2 / ((a : ℝ) + b) - b⁻¹) b := by
  have hd := cauchy_expectation_has_deriv_at gamma a ha b hb
  have hb' : b.toNNReal ≠ 0 := by simpa using hb
  have hab' : a ≠ b.toNNReal := by
    intro h
    have hc := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    exact hab (by simpa [Real.coe_toNNReal b hb.le] using hc)
  have hk : Integrable (fun x : ℝ => 2*b / ((x-gamma)^2 + b^2)) (cauchyMeasure gamma a) := by
    refine (integrable_const (2/b)).mono'
      ((show Measurable (fun x : ℝ => 2*b / ((x-gamma)^2 + b^2)) by
        fun_prop).aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_le_div_iff₀ (by positivity) hb).2
    nlinarith [sq_nonneg (x-gamma)]
  rw [integral_sub hk (integrable_const _)] at hd
  have heq := cauchy_kernel_expectation gamma a b.toNNReal ha hb' hab'
  simp only [Real.coe_toNNReal b hb.le] at heq
  rw [heq] at hd
  simpa using hd

private lemma closed_expression_derivative (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun u : ℝ => 2 * Real.log (a+u) - Real.log (4*a) - Real.log u)
      (2 / (a+b) - b⁻¹) b := by
  have hd := (((((hasDerivAt_id b).const_add a).log (by positivity)).const_mul 2).sub_const
    (Real.log (4*a))).sub ((hasDerivAt_id b).log hb.ne')
  simpa [div_eq_mul_inv] using! hd

private lemma cauchy_log_expectation (gamma : ℝ) (a b : ℝ≥0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ x, Real.log (cauchyPDFReal gamma a x / cauchyPDFReal gamma b x)
      ∂cauchyMeasure gamma a) = cauchyKL gamma a gamma b := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast pos_iff_ne_zero.mpr ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast pos_iff_ne_zero.mpr hb
  simp_rw [cauchy_log_ratio gamma a b ha hb]
  let F := fun u : ℝ => ∫ x,
    Real.log a - Real.log u + Real.log ((x - gamma)^2 + u^2) -
      Real.log ((x - gamma)^2 + (a : ℝ)^2) ∂cauchyMeasure gamma a
  let G := fun u : ℝ => 2 * Real.log ((a : ℝ)+u) - Real.log (4*(a : ℝ)) - Real.log u
  have hcontinuous : ContinuousOn (fun u => F u - G u) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    exact ((cauchy_expectation_has_deriv_at gamma a ha t ht).continuousAt.sub
      (closed_expression_derivative a t ha' ht).continuousAt).continuousWithinAt
  have hderiv : ∀ t : ℝ, 0 < t → (a : ℝ) ≠ t → HasDerivAt (fun u => F u - G u) 0 t := by
    intro t ht hne
    simpa [F, G] using! (cauchy_expectation_derivative gamma a ha t ht hne).sub
      (closed_expression_derivative a t ha' ht)
  have hbase : F a - G a = 0 := by
    dsimp [F, G]
    simp only [sub_self, zero_add, integral_zero]
    rw [show (a : ℝ) + a = 2*a by ring,
      Real.log_mul (by norm_num) ha'.ne', Real.log_mul (by norm_num) ha'.ne',
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
        norm_num]
    ring
  -- The mean value argument avoids dividing by b^2-a^2 at the base point.
  have heq : F b - G b = F a - G a := by
    rcases lt_trichotomy (a : ℝ) b with hlt | heq | hgt
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u => F u - G u)
        (fun _ => 0) hlt
        (hcontinuous.mono (fun x hx => ha'.trans_le hx.1))
        (fun x hx => hderiv x (ha'.trans hx.1) hx.1.ne)
      exact sub_eq_zero.mp ((div_eq_zero_iff).mp hslope.symm |>.resolve_right
        (sub_ne_zero.mpr hlt.ne'))
    · rw [heq]
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u => F u - G u)
        (fun _ => 0) hgt
        (hcontinuous.mono (fun x hx => hb'.trans_le hx.1))
        (fun x hx => hderiv x (hb'.trans hx.1) hx.2.ne')
      exact (sub_eq_zero.mp ((div_eq_zero_iff).mp hslope.symm |>.resolve_right
        (sub_ne_zero.mpr hgt.ne'))).symm
  have hFG : F b = G b := sub_eq_zero.mp (heq.trans hbase)
  change F b = cauchyKL gamma a gamma b
  rw [hFG]
  dsimp [G, cauchyKL]
  norm_num only [sub_self, zero_pow, add_zero]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) hb'.ne']
  ring

/-- Positive-scale Cauchy laws at a common center have finite relative entropy given by
its closed form, with absolute continuity and logarithmic integrability proved explicitly. -/
theorem cauchy_measure_relative_entropy (gamma : ℝ) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    cauchyMeasure gamma a ≪ cauchyMeasure gamma b ∧
    Integrable (llr (cauchyMeasure gamma a) (cauchyMeasure gamma b)) (cauchyMeasure gamma a) ∧
    InformationTheory.klDiv (cauchyMeasure gamma a) (cauchyMeasure gamma b) =
      ENNReal.ofReal (cauchyKL gamma a gamma b) := by
  have hac := cauchy_ac gamma a b ha hb
  have hllr := cauchy_llr gamma a b ha hb
  have hint := (cauchy_log_integrable gamma a b ha hb).congr hllr.symm
  refine ⟨hac, hint, ?_⟩
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr,
    cauchy_log_expectation gamma a b ha hb]
  simp

private lemma cauchy_shift_strict (gamma omega d e : ℝ)
    (hw : 0 < omega) (hd : omega < d) (hde : d < e) :
    cauchyKL gamma (e-omega) gamma (e+omega) <
      cauchyKL gamma (d-omega) gamma (d+omega) := by
  have hdpos := hw.trans hd
  have hepos := hdpos.trans hde
  rw [shifted_cauchy_kl_eq_horizon_free_energy gamma e omega hw (hd.trans hde),
    shifted_cauchy_kl_eq_horizon_free_energy gamma d omega hw hd]
  unfold horizonFreeEnergy
  have hqd : 0 < omega/d := div_pos hw hdpos
  have hqe : 0 < omega/e := div_pos hw hepos
  have hlt : omega/e < omega/d := div_lt_div_of_pos_left hw hdpos hde
  have hqd1 : omega/d < 1 := (div_lt_one hdpos).2 hd
  have hs1 : (omega/d)^2 < 1 := by nlinarith
  have hsq : (omega/e)^2 < (omega/d)^2 := (sq_lt_sq₀ hqe.le hqd.le).2 hlt
  apply neg_lt_neg
  apply Real.strictMonoOn_log
  · change 0 < 1 - (omega/d)^2
    linarith
  · change 0 < 1 - (omega/e)^2
    linarith
  · linarith

open Filter
open scoped Topology

private lemma cauchy_measure_shift_value (gamma d w : ℝ) (hw : 0 < w) (hwd : w < d) :
    InformationTheory.klDiv (cauchyMeasure gamma (d-w).toNNReal)
      (cauchyMeasure gamma (d+w).toNNReal) = ENNReal.ofReal (cauchyKL gamma (d-w) gamma (d+w)) := by
  have hm : 0 < d-w := by linarith
  have hp : 0 < d+w := by linarith
  simpa [Real.coe_toNNReal _ hm.le, Real.coe_toNNReal _ hp.le] using
    (cauchy_measure_relative_entropy gamma (d-w).toNNReal (d+w).toNNReal
      (by simpa using hm) (by simpa using hp)).2.2

private lemma cauchy_measure_boundary (gamma delta : ℝ) (hd : 0 < delta) :
    Tendsto (fun w : ℝ => InformationTheory.klDiv
      (cauchyMeasure gamma (delta-w).toNNReal) (cauchyMeasure gamma (delta+w).toNNReal))
      (𝓝[<] delta) (𝓝 ∞) := by
  have hpos : ∀ᶠ w : ℝ in 𝓝[<] delta, 0 < w :=
    (eventually_gt_nhds hd).filter_mono nhdsWithin_le_nhds
  have hdomain : ∀ᶠ w : ℝ in 𝓝[<] delta, 0 < w ∧ w < delta := by
    filter_upwards [hpos, self_mem_nhdsWithin] with w hw hwd
    exact ⟨hw, hwd⟩
  have hzero : Tendsto (fun w : ℝ => 1-(w/delta)^2) (𝓝[<] delta) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun w : ℝ => 1-(w/delta)^2) (𝓝[<] delta)
          (𝓝 (1-(delta/delta)^2)) :=
        ((continuous_const.sub ((continuous_id.div_const delta).pow 2)).tendsto delta).mono_left
          nhdsWithin_le_nhds
      simpa [hd.ne'] using hc
    · filter_upwards [hdomain] with w hw
      change 0 < 1-(w/delta)^2
      have hq : 0 < w/delta := div_pos hw.1 hd
      have hq1 : w/delta < 1 := (div_lt_one hd).2 hw.2
      nlinarith
  have hlog := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hzero)
  apply (ENNReal.tendsto_ofReal_atTop.comp hlog).congr'
  filter_upwards [hdomain] with w hw
  rw [cauchy_measure_shift_value gamma delta w hw.1 hw.2,
    shifted_cauchy_kl_eq_horizon_free_energy gamma delta w hw.1 hw.2]
  rfl

/-- Common positive scale shifts strictly decrease relative entropy; admissible negative
shifts strictly increase it, and the one-sided vanishing-scale boundary diverges. -/
theorem cauchy_poisson_coarse_graining (gamma delta omega : ℝ)
    (hw : 0 < omega) (hwd : omega < delta) :
    (∀ h : ℝ, 0 < h →
      InformationTheory.klDiv (cauchyMeasure gamma (delta+h-omega).toNNReal)
        (cauchyMeasure gamma (delta+h+omega).toNNReal) <
      InformationTheory.klDiv (cauchyMeasure gamma (delta-omega).toNNReal)
        (cauchyMeasure gamma (delta+omega).toNNReal)) ∧
    (∀ h : ℝ, h < 0 → omega < delta+h →
      InformationTheory.klDiv (cauchyMeasure gamma (delta-omega).toNNReal)
        (cauchyMeasure gamma (delta+omega).toNNReal) <
      InformationTheory.klDiv (cauchyMeasure gamma (delta+h-omega).toNNReal)
        (cauchyMeasure gamma (delta+h+omega).toNNReal)) ∧
    Tendsto (fun w : ℝ => InformationTheory.klDiv
      (cauchyMeasure gamma (delta-w).toNNReal) (cauchyMeasure gamma (delta+w).toNNReal))
      (𝓝[<] delta) (𝓝 ∞) := by
  refine ⟨?_, ?_, cauchy_measure_boundary gamma delta (hw.trans hwd)⟩
  · intro h hh
    have hwh : omega < delta+h := by linarith
    rw [cauchy_measure_shift_value gamma (delta+h) omega hw hwh,
      cauchy_measure_shift_value gamma delta omega hw hwd]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (cauchy_kl_divergence_nonneg gamma (delta+h-omega) gamma (delta+h+omega)
        (by linarith) (by linarith))).2
    exact cauchy_shift_strict gamma omega delta (delta+h) hw hwd (by linarith)
  · intro h hh hwh
    rw [cauchy_measure_shift_value gamma delta omega hw hwd,
      cauchy_measure_shift_value gamma (delta+h) omega hw hwh]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (cauchy_kl_divergence_nonneg gamma (delta-omega) gamma (delta+omega)
        (by linarith) (by linarith))).2
    exact cauchy_shift_strict gamma omega (delta+h) delta hw hwh (by linarith)

#print axioms cauchy_measure_relative_entropy
#print axioms cauchy_poisson_coarse_graining

end D5.S3.Divergence.CauchyMeasureEntropy
