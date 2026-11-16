/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diagonal source-amplitude differentiation identifies the actual external jet. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution

/-! The diagonal derivative uses the actual source column and its rank-one derivative. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open OriginalGaussianAllIndexResolvent OriginalGaussianExternalResolvent
open OriginalGaussianBilinearTranspose
open OriginalGaussianExternalFrequency OriginalGaussianExternalDisplacement
open OriginalGaussianExternalRadial OriginalGaussianExternalMoments
open OriginalGaussianSourceMeans OriginalGaussianSourceEvaluation
open D5.S3.Analytic.OriginalHalfBinomialPeriod

/-- The derivative contains both the frequency and the original inverse-column jet. -/
theorem hasDerivAt_radial_sourceExternal (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ => sourceExternal out p (Real.sqrt u : ℂ))
      (-(sourceMoment out p r + sourceJetMoment out p r) /
        (2 * (r : ℂ) * period r)) r := by
  let z : ℂ := Real.sqrt r
  let X := externalVector out p z
  let C := radialColumn r
  let D := frequencyVector out p z
  have hz : ‖z‖ < 1 := radial_norm_lt_one hr1
  have hx : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hF : period (r : ℂ) ≠ 0 := OriginalGaussianPeriodIdentity.period_ne_zero hx
  have hs0 : (Real.sqrt (1 - r) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by linarith : 0 < 1 - r)).ne'
  have he (e : Bool) (k : ℕ) :
      sourceBilinearFunctional (externalVector e k z) C = sourceExternal e k z :=
    (source_pairings_explicit hz e k).2.2.1
  have ha (e : Bool) (k : ℕ) :
      sourceExternal e k z = 1 - sourceAmplitude e k r / period r := by
    have hh := sourceExternal_evaluation e k hz
    have hs : z ^ 2 = (r : ℂ) := by
      dsimp only [z]
      exact_mod_cast Real.sq_sqrt hr.le
    rw [hs] at hh
    linear_combination -hh
  have hD : sourceBilinearFunctional D C = -sourceMoment out p r / period r := by
    dsimp only [D, frequencyVector]
    rw [sourceBilinearFunctional_smul_left, sourceBilinearFunctional_comm, map_sub]
    simp only [sourceBilinearFunctional_comm C (externalVector _ _ z), he, ha]
    rw [sourceMoment_eq_modeFrequency out p hx]
    simp only [modeFrequency]
    ring
  have hC := congrArg (sourceBilinearFunctional X)
    (radial_column_derivative_scaled hr hr1)
  simp only [map_smul, smul_eq_mul] at hC
  rw [(source_moment_pairings out p hr hr1).2] at hC
  have hnorm : (radialNormalization r : ℂ) =
      1 / ((Real.sqrt (1 - r) : ℂ) * period r) := by
    rw [period_ofReal]
    simp only [radialNormalization, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul]
  rw [hnorm] at hC
  have hCd : sourceBilinearFunctional X (radialColumnDerivative r) =
      -sourceJetMoment out p r / (2 * (r : ℂ) * period r) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hr0) hF)).mpr
    field_simp [hs0, hF] at hC
    linear_combination hC
  have hd := (hasDerivAt_radial_externalVector out p hr hr1).star.inner ℂ
    (hasDerivAt_radial_column hr hr1)
  have hfun : (fun u : ℝ => sourceExternal out p (Real.sqrt u : ℂ)) =ᶠ[𝓝 r]
      (fun u => sourceBilinearFunctional (externalVector out p (Real.sqrt u : ℂ))
        (radialColumn u)) := by
    filter_upwards [isOpen_Iio.mem_nhds hr1] with u hu
    exact (source_pairings_explicit (radial_norm_lt_one hu) out p).2.2.1.symm
  apply (hd.congr_of_eventuallyEq hfun).congr_deriv
  change sourceBilinearFunctional X (radialColumnDerivative r) +
    sourceBilinearFunctional ((1 / (2 * (r : ℂ))) • D) C = _
  rw [sourceBilinearFunctional_smul_left, hD, hCd]
  field_simp [hr0, hF]
  ring

/-- The total diagonal derivative of A is determined without termwise jet substitution. -/
theorem hasDerivAt_radial_sourceAmplitude (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ => sourceAmplitude out p (u : ℂ))
      (shiftedCentralDerivative r 0 * sourceAmplitude out p r / period r +
        (sourceMoment out p r + sourceJetMoment out p r) / (2 * (r : ℂ))) r := by
  have hx : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hF : period (r : ℂ) ≠ 0 := OriginalGaussianPeriodIdentity.period_ne_zero hx
  have hperiod := (central_hasDerivAt hx 0).comp_ofReal
  have hd := hperiod.mul ((hasDerivAt_const r (1 : ℂ)).sub
    (hasDerivAt_radial_sourceExternal out p hr hr1))
  have hf : (fun u : ℝ => sourceAmplitude out p (u : ℂ)) =ᶠ[𝓝 r]
      (fun u => shiftedCentralSeries (u : ℂ) 0 *
        (1 - sourceExternal out p (Real.sqrt u : ℂ))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hr, hr1⟩] with u hu
    have hs : (Real.sqrt u : ℂ) ^ 2 = (u : ℂ) := by
      exact_mod_cast Real.sq_sqrt hu.1.le
    have he := sourceExternal_evaluation out p (radial_norm_lt_one hu.2)
    rw [hs] at he
    rw [← period_eq_central, he]
    have hFu : period (u : ℂ) ≠ 0 := OriginalGaussianPeriodIdentity.period_ne_zero (by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1] using hu.2)
    field_simp [hFu]
  apply (hd.congr_of_eventuallyEq hf).congr_deriv
  have he := sourceExternal_evaluation out p (radial_norm_lt_one hr1)
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast Real.sq_sqrt hr.le
  rw [hs] at he
  simp only [Pi.sub_apply] 
  rw [← period_eq_central, he]
  field_simp [hr0, hF]
  ring

/-- The actual jet is recovered from the diagonal derivative and the mode difference. -/
theorem sourceJetMoment_eq_derivative (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    sourceJetMoment out p r =
      2 * (r : ℂ) * deriv (fun u : ℝ => sourceAmplitude out p (u : ℂ)) r -
        modeFrequency out p (fun e k => sourceAmplitude e k r) -
        2 * (r : ℂ) * sourceAmplitude out p r * shiftedCentralDerivative r 0 / period r := by
  have hx : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  rw [(hasDerivAt_radial_sourceAmplitude out p hr hr1).deriv,
    ← sourceMoment_eq_modeFrequency out p hx]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hr0]
  ring

/-- The genuine displacement and radial equations now use only A and its total derivative. -/
theorem external_source_equations (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    let z : ℂ := Real.sqrt r
    let U := fun e k => modeFrequency e k (fun f l => sourceAmplitude f l (r : ℂ))
    let V := fun e k =>
      2 * (r : ℂ) * deriv (fun u : ℝ => sourceAmplitude e k (u : ℂ)) r - U e k -
        2 * (r : ℂ) * sourceAmplitude e k r * shiftedCentralDerivative r 0 / period r
    (modeFrequency out p (fun e k => externalJ e k out' q z) +
      modeFrequency out' q (fun e k => externalJ out p e k z) =
      (1 - (r : ℂ)) * (U out p * V out' q + V out p * U out' q) / 2) ∧
    (modeFrequency out p (fun e k => externalT e k out' q z) -
      modeFrequency out' q (fun e k => externalT out p e k z) =
      (1 - (r : ℂ)) * (U out p * V out' q - V out p * U out' q) / 2) ∧
    HasDerivAt (fun u : ℝ => externalT out p out' q (Real.sqrt u : ℂ))
      ((modeFrequency out p (fun e k => externalT e k out' q z) +
        modeFrequency out' q (fun e k => externalT out p e k z) +
        (1 - (r : ℂ)) / 2 * (V out p * V out' q - U out p * U out' q)) /
        (2 * (r : ℂ))) r := by
  have hx : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hd := external_displacement_explicit out p out' q hr hr1
  have ht := OriginalGaussianExternalEvolution.externalT_radial_equation out p out' q hr hr1
  simp only [sourceJetMoment_eq_derivative _ _ hr hr1,
    sourceMoment_eq_modeFrequency _ _ hx] at hd ht
  exact ⟨hd.1, hd.2, ht⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
