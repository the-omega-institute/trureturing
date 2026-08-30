/- GID: D5/S3/Fourier/CompletionConstants/LiCaratheodoryIdentity
   generality: I
   mirror-B: D5/B/S3/Fourier/CompletionConstants/LiCaratheodoryIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Li-Caratheodory identity from the completed xi reading and its Mobius coordinate. -/

import D5.S3.Zeros.Endpoints.XiEndpointValues
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace D5.S3.Fourier.CompletionConstants.LiCaratheodoryIdentity

open Complex
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues

-- The source's coordinate `s(z)=1/(1-z)` and the associated generating reading.
noncomputable def mobiusCoordinate (z : ℂ) : ℂ := 1 / (1 - z)

noncomputable def liGenerating (z : ℂ) : ℂ :=
  xiReading (mobiusCoordinate z) /
    xiReading 1

-- The first coefficient is the logarithmic derivative of the normalized generating reading at zero.
noncomputable def lambdaOne : ℂ := logDeriv liGenerating 0

noncomputable def liCaratheodory (z : ℂ) : ℂ :=
  (1 - z) ^ 2 / lambdaOne * logDeriv liGenerating z

private lemma xi_one_ne_zero : xiReading 1 ≠ 0 := by
  rw [xi_reading_endpoint_values.2]
  norm_num

private lemma mobius_denominator_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have hz' : z = 1 := (sub_eq_zero.mp h).symm
  subst z
  norm_num at hz

private lemma differentiableAt_mobius {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ mobiusCoordinate z := by
  unfold mobiusCoordinate
  exact (differentiableAt_const (c := (1 : ℂ))).div
    ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
    (mobius_denominator_ne_zero hz)

private lemma deriv_mobius {z : ℂ} (hz : ‖z‖ < 1) :
    deriv mobiusCoordinate z = 1 / (1 - z) ^ 2 := by
  have hden : (1 - z : ℂ) ≠ 0 := mobius_denominator_ne_zero hz
  have hderiv0 :=
    (hasDerivAt_inv hden).comp z ((hasDerivAt_id z).const_sub (1 : ℂ))
  have hderiv : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z) ^ 2)⁻¹ z := by
    simpa [Function.comp_def, one_div, div_eq_mul_inv] using hderiv0
  change deriv (fun w : ℂ => 1 / (1 - w)) z = 1 / (1 - z) ^ 2
  have hderiv' : HasDerivAt (fun w : ℂ => 1 / (1 - w)) ((1 - z) ^ 2)⁻¹ z := by
    simpa [one_div] using hderiv
  simpa [one_div] using hderiv'.deriv

private lemma liGenerating_eq_mul :
    liGenerating = fun z => xiReading (mobiusCoordinate z) * (xiReading 1)⁻¹ := by
  funext z
  simp [liGenerating, div_eq_mul_inv]

private lemma logDeriv_liGenerating {z : ℂ} (hz : ‖z‖ < 1) :
    logDeriv liGenerating z =
      logDeriv xiReading (mobiusCoordinate z) * deriv mobiusCoordinate z := by
  rw [liGenerating_eq_mul, logDeriv_mul_const z (xiReading 1)⁻¹]
  · rw [show (fun u : ℂ => xiReading (mobiusCoordinate u)) =
        xiReading ∘ mobiusCoordinate from rfl]
    exact logDeriv_comp xi_reading_differentiable.differentiableAt
      (differentiableAt_mobius hz)
  · exact inv_ne_zero (xi_one_ne_zero)

private lemma lambdaOne_ne_zero (hpositive : 0 < lambdaOne.re) : lambdaOne ≠ 0 := by
  intro hzero
  rw [hzero] at hpositive
  norm_num at hpositive

theorem li_caratheodory_identity (z : ℂ) (hz : ‖z‖ < 1)
    (hpositive : 0 < lambdaOne.re) :
    liCaratheodory z = (1 / lambdaOne) * logDeriv xiReading (mobiusCoordinate z) ∧
      (1 / 2 : ℝ) < (mobiusCoordinate z).re ∧
      liCaratheodory 0 = 1 := by
  have hnonzero : lambdaOne ≠ 0 := lambdaOne_ne_zero hpositive
  refine ⟨?_, ?_, ?_⟩
  · rw [liCaratheodory, logDeriv_liGenerating hz, deriv_mobius hz]
    have hden : (1 - z : ℂ) ≠ 0 := mobius_denominator_ne_zero hz
    field_simp [hnonzero, hden]
  · unfold mobiusCoordinate
    have hmobius_re :
        (1 / (1 - z)).re =
          (1 - z.re) / ((1 - z.re) ^ 2 + z.im ^ 2) := by
      simp [Complex.normSq_apply]
      ring
    rw [hmobius_re]
    have hnorm : ‖z‖ ^ 2 < (1 : ℝ) := by
      nlinarith [norm_nonneg z]
    have hxy : z.re ^ 2 + z.im ^ 2 < (1 : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hnorm
      simpa [pow_two] using hnorm
    have hdenpos : 0 < (1 - z.re) ^ 2 + z.im ^ 2 := by
      nlinarith [sq_nonneg (1 - z.re), sq_nonneg z.im]
    apply (lt_div_iff₀ hdenpos).2
    nlinarith
  · unfold liCaratheodory lambdaOne
    simp only [sub_zero, one_pow]
    simpa [lambdaOne] using one_div_mul_cancel (lambdaOne_ne_zero hpositive)

-- Reverse probe: the public equality recovers the completed logarithmic derivative.
example (z : ℂ) (_hz : ‖z‖ < 1) (hpositive : 0 < lambdaOne.re)
    (hidentity : liCaratheodory z =
      (1 / lambdaOne) * logDeriv xiReading (mobiusCoordinate z)) :
    logDeriv xiReading (mobiusCoordinate z) =
      lambdaOne * liCaratheodory z := by
  have hnonzero : lambdaOne ≠ 0 := lambdaOne_ne_zero hpositive
  rw [hidentity]
  field_simp [hnonzero]

-- Trivialization probe: zero cannot satisfy the sourced positive normalization domain.
example : ¬ (0 < lambdaOne.re ∧ lambdaOne = 0) := by
  intro h
  rw [h.2] at h
  norm_num at h

#print axioms li_caratheodory_identity

end D5.S3.Fourier.CompletionConstants.LiCaratheodoryIdentity
