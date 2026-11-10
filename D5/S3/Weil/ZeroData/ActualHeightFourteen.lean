/- GID: D5/S3/Weil/ZeroData/ActualHeightFourteen
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZeroData/ActualHeightFourteen.actual_height_gt_fourteen; premises=D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_evaluatedMass_upper,D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_kernel_bounds
   digest: Exclude every actual ordinate through fourteen and bound the full occurrence inverse-square mass. -/

import D5.S3.Weil.ZeroData.ActualHeightFourteenNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Weil.Convention
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate Topology

private def h14EightWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 56))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14EightDefect : ℝ := 15 / 2 * firstLiMass - (logDeriv xiReading 8).re

private theorem actual_h14Eight_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    8 - actualData.zero n ≠ 0 ∧ 7 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Eight_ne_zero : xiReading (8 : ℂ) ≠ 0 := by
  have hz : riemannZeta (8 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (8 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (8 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Eight_identity (n : ℕ) :
    8 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (8 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (8 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      420 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 56))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Eight_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 56 =
      (8 - actualData.zero n) * (7 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 56 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 8 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Eight_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 56))))
      ((((15 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 8) / 420) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 8 xi_h14Eight_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (8 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 8 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (8 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 420 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Eight_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 420) *
      reflected_h14Eight_identity n
  · rw [heightRefinement_one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Eight_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14EightWeight (actualData.zero n)) (h14EightDefect / 420) := by
  simpa [h14EightWeight, h14EightDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Eight_hasSum

private theorem xi_h14Eight_logDeriv :
    logDeriv xiReading (8 : ℂ) =
      ((199 / 168 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 8 / riemannZeta 8 := by
  have hz : riemannZeta (8 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (8 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (8 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (8 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (8 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (8 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (8 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 8 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (4 : ℂ) =
      ((11 / 6 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 3
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (8 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (8 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (8 : ℂ) / 2 = 4 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14EightQ : ℝ := (-deriv riemannZeta (8 : ℂ) / riemannZeta 8).re

private theorem h14EightDefect_evaluation : h14EightDefect =
    2321 / 168 + 8 * Real.eulerMascheroniConstant - 15 * Real.log 2 -
      7 * Real.log Real.pi + h14EightQ := by
  rw [h14EightDefect, firstLiMass_split, xi_h14Eight_logDeriv]
  unfold h14EightQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

/-- The actual reflected-resolvent kernel. -/
private def h14TenWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 90))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14TenDefect : ℝ := 19 / 2 * firstLiMass - (logDeriv xiReading 10).re

private theorem actual_h14Ten_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    10 - actualData.zero n ≠ 0 ∧ 9 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Ten_ne_zero : xiReading (10 : ℂ) ≠ 0 := by
  have hz : riemannZeta (10 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (10 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (10 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Ten_identity (n : ℕ) :
    10 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (10 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (10 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      855 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 90))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Ten_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 90 =
      (10 - actualData.zero n) * (9 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 90 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 10 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Ten_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 90))))
      ((((19 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 10) / 855) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 10 xi_h14Ten_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (10 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 10 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (10 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 855 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Ten_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 855) *
      reflected_h14Ten_identity n
  · rw [heightRefinement_one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Ten_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14TenWeight (actualData.zero n)) (h14TenDefect / 855) := by
  simpa [h14TenWeight, h14TenDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Ten_hasSum

private theorem xi_h14Ten_logDeriv :
    logDeriv xiReading (10 : ℂ) =
      ((451 / 360 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 10 / riemannZeta 10 := by
  have hz : riemannZeta (10 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (10 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (10 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (10 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (10 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (10 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (10 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 10 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (5 : ℂ) =
      ((25 / 12 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 4
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (10 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (10 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (10 : ℂ) / 2 = 5 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14TenQ : ℝ := (-deriv riemannZeta (10 : ℂ) / riemannZeta 10).re

private theorem h14TenDefect_evaluation : h14TenDefect =
    6389 / 360 + 10 * Real.eulerMascheroniConstant - 19 * Real.log 2 -
      9 * Real.log Real.pi + h14TenQ := by
  rw [h14TenDefect, firstLiMass_split, xi_h14Ten_logDeriv]
  unfold h14TenQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

/-- The actual reflected-resolvent kernel. -/
private def h14TwelveWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 132))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14TwelveDefect : ℝ := 23 / 2 * firstLiMass - (logDeriv xiReading 12).re

private theorem actual_h14Twelve_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    12 - actualData.zero n ≠ 0 ∧ 11 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Twelve_ne_zero : xiReading (12 : ℂ) ≠ 0 := by
  have hz : riemannZeta (12 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (12 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (12 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Twelve_identity (n : ℕ) :
    12 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (12 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (12 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      1518 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 132))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Twelve_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 132 =
      (12 - actualData.zero n) * (11 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 132 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 12 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Twelve_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 132))))
      ((((23 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 12) / 1518) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 12 xi_h14Twelve_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (12 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 12 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (12 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 1518 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Twelve_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 1518) *
      reflected_h14Twelve_identity n
  · rw [heightRefinement_one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Twelve_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14TwelveWeight (actualData.zero n)) (h14TwelveDefect / 1518) := by
  simpa [h14TwelveWeight, h14TwelveDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Twelve_hasSum

private theorem xi_h14Twelve_logDeriv :
    logDeriv xiReading (12 : ℂ) =
      ((579 / 440 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 12 / riemannZeta 12 := by
  have hz : riemannZeta (12 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (12 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (12 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (12 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (12 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (12 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (12 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 12 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (6 : ℂ) =
      ((137 / 60 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 5
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (12 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (12 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (12 : ℂ) / 2 = 6 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14TwelveQ : ℝ := (-deriv riemannZeta (12 : ℂ) / riemannZeta 12).re

private theorem h14TwelveDefect_evaluation : h14TwelveDefect =
    9541 / 440 + 12 * Real.eulerMascheroniConstant - 23 * Real.log 2 -
      11 * Real.log Real.pi + h14TwelveQ := by
  rw [h14TwelveDefect, firstLiMass_split, xi_h14Twelve_logDeriv]
  unfold h14TwelveQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

/-- The actual reflected-resolvent kernel. -/
private def h14FourteenWeight (rho : ℂ) : ℝ :=
  (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 182))).re

/-- The exact real first-resolvent defect, before evaluating any special functions. -/
private def h14FourteenDefect : ℝ := 27 / 2 * firstLiMass - (logDeriv xiReading 14).re

private theorem actual_h14Fourteen_denominators (n : ℕ) :
    actualData.zero n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    14 - actualData.zero n ≠ 0 ∧ 13 + actualData.zero n ≠ 0 := by
  have hs := (actualData.zero_isNontrivial n).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals have hr := congrArg Complex.re he
  all_goals simp only [Complex.add_re, Complex.sub_re, Complex.zero_re,
    Complex.one_re, Complex.re_ofNat] at hr
  all_goals linarith

private theorem xi_h14Fourteen_ne_zero : xiReading (14 : ℂ) ≠ 0 := by
  have hz : riemannZeta (14 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hg : Complex.Gammaℝ (14 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have he := (Zeta23.WeilEF.completedZeta_eventuallyEq_mul
    (s := (14 : ℂ)) (by norm_num)).eq_of_nhds
  rw [xi_reading_eq_completed_zeta (by norm_num) (by norm_num),
    completedZetaReading, he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
    (by norm_num)) (mul_ne_zero hg hz)

private theorem reflected_h14Fourteen_identity (n : ℕ) :
    14 * (1 / (actualData.zero n * (1 - actualData.zero n))) -
      (1 / 2 : ℂ) *
        ((1 / (14 - actualData.zero n) + 1 / actualData.zero n) +
          (1 / (14 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n))) =
      2457 * (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 182))) := by
  obtain ⟨h0, h1, h6, h5⟩ := actual_h14Fourteen_denominators n
  have hf : actualData.zero n * (1 - actualData.zero n) + 182 =
      (14 - actualData.zero n) * (13 + actualData.zero n) := by ring
  have hq := mul_ne_zero h0 h1
  have hc : actualData.zero n * (1 - actualData.zero n) + 182 ≠ 0 := by
    rw [hf]; exact mul_ne_zero h6 h5
  have hr : 14 - (1 - actualData.zero n) ≠ 0 := by
    convert h5 using 1 <;> ring
  field_simp [h0, h1, h6, hr, hq, hc]
  <;> ring

private theorem actual_complex_h14Fourteen_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / ((actualData.zero n * (1 - actualData.zero n)) *
        (actualData.zero n * (1 - actualData.zero n) + 182))))
      ((((27 / 2 * firstLiMass : ℝ) : ℂ) - logDeriv xiReading 14) / 2457) := by
  have hx1 : xiReading 1 ≠ 0 := by rw [xi_reading_endpoint_values.2]; norm_num
  have h1 := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have h6 := xi_reading_normalized_resolvent_hasSum actualData 14 xi_h14Fourteen_ne_zero
  have href : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      (1 / (14 - (1 - actualData.zero n)) + 1 / (1 - actualData.zero n)))
      (logDeriv xiReading 14 - logDeriv xiReading 0) := by
    simpa only [Function.comp_def, actualData.multiplicity_reflection,
      actualData.zero_reflection] using actualData.reflection.hasSum_iff.mpr h6
  have hc := ((h1.mul_left (14 : ℂ)).sub
    ((h6.add href).mul_left (1 / 2 : ℂ))).mul_left (1 / 2457 : ℂ)
  convert hc using 1
  · funext n
    obtain ⟨h0, h1, _, _⟩ := actual_h14Fourteen_denominators n
    have hep : 1 / (1 - actualData.zero n) + 1 / actualData.zero n =
        1 / (actualData.zero n * (1 - actualData.zero n)) := by
      field_simp [h0, h1]<;> ring
    rw [hep]
    linear_combination (-(actualData.multiplicity n : ℂ) / 2457) *
      reflected_h14Fourteen_identity n
  · rw [heightRefinement_one_endpoint_logDeriv, zero_endpoint_logDeriv]
    push_cast
    ring

private theorem actual_h14Fourteen_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14FourteenWeight (actualData.zero n)) (h14FourteenDefect / 2457) := by
  simpa [h14FourteenWeight, h14FourteenDefect, Complex.mul_re, Complex.div_ofNat_re] using
    Complex.hasSum_re actual_complex_h14Fourteen_hasSum

private theorem xi_h14Fourteen_logDeriv :
    logDeriv xiReading (14 : ℂ) =
      ((4999 / 3640 - Real.eulerMascheroniConstant / 2 -
        Real.log Real.pi / 2 : ℝ) : ℂ) +
        deriv riemannZeta 14 / riemannZeta 14 := by
  have hz : riemannZeta (14 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hc : completedRiemannZeta (14 : ℂ) ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (s := (14 : ℂ)) (by norm_num)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) hz
  have hnear : xiReading =ᶠ[nhds (14 : ℂ)]
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) := by
    filter_upwards [eventually_ne_nhds (show (14 : ℂ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (14 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
    rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading]
    ring
  have heq : logDeriv xiReading (14 : ℂ) = logDeriv
      (fun s : ℂ => (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s)) 14 := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  have hdig : Complex.digamma (7 : ℂ) =
      ((49 / 20 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    have h := Complex.digamma_nat_add_one 6
    norm_num [harmonic, Finset.sum_range_succ] at h
    convert h using 1 <;> push_cast <;> ring
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (14 : ℂ) (by norm_num) hc (by fun_prop)
      (differentiableAt_completedZeta (by norm_num) (by norm_num)),
    logDeriv_fun_mul (14 : ℂ) (by norm_num) (by norm_num) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta _ (by norm_num) hz (by norm_num),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by norm_num)]
  norm_num only [show (14 : ℂ) / 2 = 7 by norm_num, hdig]
  simp only [logDeriv_apply]
  norm_num [deriv_id'', deriv_sub_const]
  push_cast
  ring

/-- The actual von Mangoldt series, not the logarithm majorant. -/
private def h14FourteenQ : ℝ := (-deriv riemannZeta (14 : ℂ) / riemannZeta 14).re

private theorem h14FourteenDefect_evaluation : h14FourteenDefect =
    93281 / 3640 + 14 * Real.eulerMascheroniConstant - 27 * Real.log 2 -
      13 * Real.log Real.pi + h14FourteenQ := by
  rw [h14FourteenDefect, firstLiMass_split, xi_h14Fourteen_logDeriv]
  unfold h14FourteenQ
  simp only [neg_div, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring


private def h14Mass : ℝ :=
  sixDefect / 3990729600 - h14EightDefect / 3555377280 +
    h14TenDefect / 6739588800 - h14TwelveDefect / 24711825600 +
    h14FourteenDefect / 216459734400

private theorem h14Shift_ne_zero (n : ℕ) (s : ℕ) (hs : 2 ≤ s) :
    actualData.zero n * (1 - actualData.zero n) + (s : ℂ) * ((s : ℂ) - 1) ≠ 0 := by
  have hs0 : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  have hstrip := (actualData.zero_isNontrivial n).2
  have he : actualData.zero n * (1 - actualData.zero n) + (s : ℂ) * ((s : ℂ) - 1) =
      ((s : ℂ) - actualData.zero n) * ((s : ℂ) - 1 + actualData.zero n) := by ring
  rw [he]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re] at hr
    linarith
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
      Complex.one_re, Complex.zero_re] at hr
    linarith

private theorem h14PartialFractions (n : ℕ) :
    h14Kernel (actualData.zero n) =
      (165 / 3990729600 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 30))) -
      (420 / 3555377280 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 56))) +
      (855 / 6739588800 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 90))) -
      (1518 / 24711825600 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 132))) +
      (2457 / 216459734400 : ℂ) *
        (1 / ((actualData.zero n * (1 - actualData.zero n)) *
          (actualData.zero n * (1 - actualData.zero n) + 182))) := by
  obtain ⟨h0, h1, _, _⟩ := heightRefinement_actual_six_denominators n
  have hq := mul_ne_zero h0 h1
  have h30 : actualData.zero n * (1 - actualData.zero n) + 30 ≠ 0 := by
    convert h14Shift_ne_zero n 6 (by norm_num) using 1 <;> norm_num
  have h56 : actualData.zero n * (1 - actualData.zero n) + 56 ≠ 0 := by
    convert h14Shift_ne_zero n 8 (by norm_num) using 1 <;> norm_num
  have h90 : actualData.zero n * (1 - actualData.zero n) + 90 ≠ 0 := by
    convert h14Shift_ne_zero n 10 (by norm_num) using 1 <;> norm_num
  have h132 : actualData.zero n * (1 - actualData.zero n) + 132 ≠ 0 := by
    convert h14Shift_ne_zero n 12 (by norm_num) using 1 <;> norm_num
  have h182 : actualData.zero n * (1 - actualData.zero n) + 182 ≠ 0 := by
    convert h14Shift_ne_zero n 14 (by norm_num) using 1 <;> norm_num
  unfold h14Kernel
  field_simp [hq, h30, h56, h90, h132, h182]
  <;> ring

private theorem h14Weight_partialFractions (n : ℕ) :
    h14Weight (actualData.zero n) =
      (165 / 3990729600 : ℝ) * sixWeight (actualData.zero n) -
      (420 / 3555377280 : ℝ) * h14EightWeight (actualData.zero n) +
      (855 / 6739588800 : ℝ) * h14TenWeight (actualData.zero n) -
      (1518 / 24711825600 : ℝ) * h14TwelveWeight (actualData.zero n) +
      (2457 / 216459734400 : ℝ) * h14FourteenWeight (actualData.zero n) := by
  have h := congrArg Complex.re (h14PartialFractions n)
  simpa only [h14Weight, sixWeight, h14EightWeight, h14TenWeight,
    h14TwelveWeight, h14FourteenWeight, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, mul_zero,
    zero_div, add_zero] using h

private theorem h14_hasSum :
    HasSum (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      h14Weight (actualData.zero n)) h14Mass := by
  have h := ((((heightRefinement_actual_six_hasSum.mul_left (165 / 3990729600 : ℝ)).sub
    (actual_h14Eight_hasSum.mul_left (420 / 3555377280 : ℝ))).add
    (actual_h14Ten_hasSum.mul_left (855 / 6739588800 : ℝ))).sub
    (actual_h14Twelve_hasSum.mul_left (1518 / 24711825600 : ℝ))).add
    (actual_h14Fourteen_hasSum.mul_left (2457 / 216459734400 : ℝ))
  convert h using 1
  · funext n
    rw [h14Weight_partialFractions]
    ring
  · unfold h14Mass
    ring

private theorem h14Mass_evaluation : h14Mass =
    66493177 / 143006288128704000 +
      (4 / 12649365729) * Real.eulerMascheroniConstant -
      Real.log 2 / 1816214400 - (9487 / 40477970332800) * Real.log Real.pi +
      (-deriv riemannZeta (6 : ℂ) / riemannZeta 6).re / 3990729600 -
      (-deriv riemannZeta (8 : ℂ) / riemannZeta 8).re / 3555377280 +
      (-deriv riemannZeta (10 : ℂ) / riemannZeta 10).re / 6739588800 -
      (-deriv riemannZeta (12 : ℂ) / riemannZeta 12).re / 24711825600 +
      (-deriv riemannZeta (14 : ℂ) / riemannZeta 14).re / 216459734400 := by
  rw [h14Mass, heightRefinement_sixDefect_evaluation, h14EightDefect_evaluation,
    h14TenDefect_evaluation, h14TwelveDefect_evaluation, h14FourteenDefect_evaluation]
  unfold sixQ h14EightQ h14TenQ h14TwelveQ h14FourteenQ
  norm_num only [Nat.cast_ofNat]
  ring


private theorem h14Mass_upper :
    h14Mass ≤ 72126772613108177 / 15194418113674800000000000000000 := by
  rw [h14Mass_evaluation]
  exact h14_evaluatedMass_upper

private theorem h14Weight_pos (n : ℕ) : 0 < h14Weight (actualData.zero n) := by
  have hstrip := (actualData.zero_isNontrivial n).2
  exact (h14_kernel_bounds _ hstrip.1 hstrip.2
    (heightRefinement_actual_ordinate_sq_gt_hundred n)).1

private theorem h14Weight_conj (rho : ℂ) : h14Weight (conj rho) = h14Weight rho := by
  have h : h14Kernel (conj rho) = conj (h14Kernel rho) := by
    simp only [h14Kernel, map_div₀, map_mul, map_add, map_sub, map_one,
      map_natCast, map_ofNat, starRingEnd_apply]
  unfold h14Weight
  rw [h, Complex.conj_re]

private theorem h14Pair_le (n : ℕ) :
    2 * ((actualData.multiplicity n : ℝ) * h14Weight (actualData.zero n)) ≤
      h14Mass := by
  classical
  have h := sum_le_hasSum ({n, actualData.conjugation n} : Finset ℕ)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (h14Weight_pos j).le) h14_hasSum
  rw [Finset.sum_pair (heightRefinement_actual_conjugation_ne n).symm,
    actualData.multiplicity_conjugation, actualData.zero_conjugation,
    h14Weight_conj] at h
  linarith only [h]

private theorem h14Low_forces_mass (n : ℕ) (hu : (actualData.zero n).im ^ 2 ≤ 196) :
    345650537 / 72636763553532703907200 ≤ h14Mass := by
  have hstrip := (actualData.zero_isNontrivial n).2
  have hl := (h14_kernel_bounds _ hstrip.1 hstrip.2
    (heightRefinement_actual_ordinate_sq_gt_hundred n)).2 hu
  have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
  have hmul : h14Weight (actualData.zero n) ≤
      (actualData.multiplicity n : ℝ) * h14Weight (actualData.zero n) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm) (h14Weight_pos n).le]
  linarith only [hl, hmul, h14Pair_le n]

private theorem h14_ordinate_sq (n : ℕ) : 196 < (actualData.zero n).im ^ 2 := by
  by_contra h
  have hl := h14Low_forces_mass n (le_of_not_gt h)
  have hu := h14Mass_upper
  have hgap : (345650537 / 72636763553532703907200 : ℝ) -
      72126772613108177 / 15194418113674800000000000000000 =
        4091911135692077535684108547 /
          349994189092536057987654937200000000000000000 := by norm_num
  have hpos : (0 : ℝ) < 4091911135692077535684108547 /
      349994189092536057987654937200000000000000000 := by norm_num
  linarith only [hl, hu, hgap, hpos]

/-- Every original nontrivial zero has absolute ordinate greater than fourteen.
Both signs and the original positive analytic multiplicities are retained. -/
theorem actual_height_gt_fourteen (rho : ℂ) (hrho : IsNontrivialZero rho) :
    14 < |rho.im| := by
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hrho
  have hu := h14_ordinate_sq n
  rw [hn] at hu
  by_contra h
  have hle : |rho.im| ≤ 14 := le_of_not_gt h
  have hp := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ 14 + |rho.im| by positivity)
  nlinarith [sq_abs rho.im]

private theorem actual_inverse_square_le_height_fourteen (n : ℕ) :
    ((actualData.zero n).im)⁻¹ ^ 2 ≤
      (197 / 196 : ℝ) * pairWeight (actualData.zero n) := by
  have hs := (actualData.zero_isNontrivial n).2
  have hlower := (heightRefinement_pairWeight_strip hs.1 hs.2).2
  have ht := actual_height_gt_fourteen (actualData.zero n)
    (actualData.zero_isNontrivial n)
  have hu : (196 : ℝ) < (actualData.zero n).im ^ 2 := by
    have hp : 0 < (|(actualData.zero n).im| - 14) *
        (|(actualData.zero n).im| + 14) :=
      mul_pos (sub_pos.mpr ht) (by linarith)
    nlinarith only [hp, sq_abs ((actualData.zero n).im)]
  have hpos : 0 < (actualData.zero n).im ^ 2 := by linarith
  calc
    ((actualData.zero n).im)⁻¹ ^ 2 = 1 / ((actualData.zero n).im ^ 2) := by
      simp only [inv_pow, one_div]
    _ ≤ (197 / 196 : ℝ) * (1 / ((actualData.zero n).im ^ 2 + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
      linarith
    _ ≤ (197 / 196 : ℝ) * pairWeight (actualData.zero n) :=
      mul_le_mul_of_nonneg_left hlower (by norm_num)

private theorem actual_weighted_inverse_square_mass_le_height_fourteen :
    (∑' n : ℕ, (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2) ≤ (197 / 196 : ℝ) * firstLiMass := by
  have hc := actual_pairWeight_hasSum.mul_left (197 / 196 : ℝ)
  have hdom : ∀ n : ℕ, (actualData.multiplicity n : ℝ) *
      ((actualData.zero n).im)⁻¹ ^ 2 ≤
        (197 / 196 : ℝ) *
          ((actualData.multiplicity n : ℝ) * pairWeight (actualData.zero n)) := by
    intro n
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (actual_inverse_square_le_height_fourteen n)
        (Nat.cast_nonneg (actualData.multiplicity n))
  simpa only [hc.tsum_eq] using
    actual_weighted_inverse_square_summable.tsum_le_tsum hdom hc.summable

/-- The complete natural-occurrence inverse-square mass has factor `197/196`.
Both signs, every distinct actual zero, and every analytic multiplicity are
preserved by the original occurrence equivalence. -/
theorem actual_inverse_square_mass_le_height_fourteen :
    (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) ≤ (197 / 196 : ℝ) * firstLiMass := by
  rw [actual_inverse_square_tsum_transport]
  exact actual_weighted_inverse_square_mass_le_height_fourteen

end D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
