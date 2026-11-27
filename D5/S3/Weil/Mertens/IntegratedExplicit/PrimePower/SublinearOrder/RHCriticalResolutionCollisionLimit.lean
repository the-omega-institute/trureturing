/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform upper pair-correlation bound yields the harmonic zeta collision limit at critical resolution. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalPairSumThreshold

/-! The vanishing long-band bound is sufficient for the critical Gaussian limit. -/

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalResolutionCollisionLimit

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalPairSumThreshold
open MeasureTheory Set
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase norm_phase)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (complexScore complexScore_continuous)
open scoped BigOperators
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (character_add)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (phase_re)
open D5.S3.Analytic.Oscillation.MontgomeryWindow
  (exponentialWeight exponentialWeight_integrable exponentialWeight_cosine
    exponentialWeight_mul_cos_integrable)
open D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open D5.S3.Analytic.Oscillation.MontgomeryWindow (montgomery)
open D5.S3.Analytic.Oscillation.MontgomeryWindow (pairCos montgomery_normalization)
open Filter
open scoped Topology
open D5.S3.Analytic.Oscillation.OrdinateCounting (CountAsymptotic count_upper)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum zetaSpectrum_countAsymptotic)
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment (cutoff_mono)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer
  (band_deficit harmonic_band_transfer)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
  (harmonicOrdinate harmonicProbability)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
  (harmonicScale harmonic_central_window_limit harmonic_multiple_log_annulus_limit_of_deficit
    harmonic_fejer_relative_control normalized_harmonic_collision_limit_of_fejer
    whole_log_window_deficit normalized_collision_eq_div_mass)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Fourier.Concentration.FejerRelativeLocalization
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Fourier.Concentration.FejerCollisionLimit
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
open D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit (pairMoment score_square_cosine)
open D5.S3.Analytic.Fourier.AngularFejerKernel
open D5.S3.Weil.ZetaExplicit.LandauUniformCutoff (actual_cutoff_landau_envelope six_lt_height)
open Finset
open D5.S3.Fourier.Concentration.FejerCollisionSecants (rampCollisionMass)

/-- Uniform little-o of the logarithm for the normalized Montgomery sum on
every fixed logarithmic band. -/
def MontgomeryUpperBoundOnLogBands (S : Spectrum) : Prop :=
  ∀ A > (1 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ Y : ℝ in atTop,
    ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
      montgomery S (t / Real.log Y) Y ≤ ε * Real.log Y

private theorem harmonic_long_deficit (rh : RiemannHypothesis)
    (hcorr : MontgomeryUpperBoundOnLogBands (zetaSpectrum rh)) (A : ℝ) (hA : 1 < A) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, Real.log T ≤ |t| → |t| ≤ A * Real.log T →
      1 / (32 * Real.log T) ≤
        1 - ‖complexScore (harmonicOrdinate rh T) (harmonicProbability rh T) t‖ := by
  classical
  let S := zetaSpectrum rh
  let ε := 1 / (64 * Real.pi)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall := cutoff_small_of_pair_bound S (zetaSpectrum_countAsymptotic rh)
    (2*A) (hcorr (2*A) (by linarith)) ε hε
  have hsmall' := (tendsto_id.const_mul_atTop (show 0 < (3:ℝ)/4 by norm_num)).eventually hsmall
  obtain ⟨L, _, hL⟩ := harmonic_band_transfer rh
  filter_upwards [eventually_ge_atTop L, eventually_ge_atTop (4 : ℝ), hsmall, hsmall'] with
    T hLT hT hTsmall hVsmall
  intro t hlo hhi
  let V := T * (3/4)
  have hTp : 0 < T := by linarith
  have hVp : 1 < V := by dsimp [V]; linarith
  have hVT : V ≤ T := by dsimp [V]; linarith
  have hlogT := Real.log_pos (show 1 < T by linarith)
  have hlogV := Real.log_pos hVp
  have hlog_l : Real.log V ≤ Real.log T := Real.log_le_log (by linarith) hVT
  have hV2 : T ≤ V^2 := by
    dsimp [V]
    nlinarith only [mul_nonneg hTp.le (show 0 ≤ T-4 by linarith), hT]
  have hlog_u : Real.log T ≤ 2 * Real.log V := by
    have hh := Real.log_le_log hTp hV2
    rwa [Real.log_pow, Nat.cast_ofNat] at hh
  have hTupper : |t| ≤ (2*A) * Real.log T := by
    apply hhi.trans
    nlinarith only [mul_nonneg hlogT.le (show 0 ≤ A by linarith)]
  have hVupper : |t| ≤ (2*A) * Real.log V := by
    apply hhi.trans
    have hm := mul_le_mul_of_nonneg_left hlog_u (show 0 ≤ A by linarith)
    nlinarith only [hm]
  have hVsmall' : ∀ t : ℝ, Real.log V ≤ |t| → |t| ≤ (2*A) * Real.log V →
      ‖∑ j ∈ S.cut V, (S.mult j : ℂ) * phase (S.gamma j) t‖ ≤ ε * (V * Real.log V) := by
    simpa only [V, id_eq, mul_comm ((3:ℝ)/4) T] using hVsmall
  have hVb' := hVsmall' t (hlog_l.trans hlo) hVupper
  have hVb : ‖∑ j ∈ S.cut V, (S.mult j : ℂ) * phase (S.gamma j) t‖ ≤
      ε * (T * Real.log T) := by
    exact hVb'.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hVT hlog_l hlogV.le hTp.le) hε.le)
  let p (j : PositiveZetaZero) := (Zeta23.zeroMult j.val : ℂ) * phase (ordinate j) t
  have hcut : positiveCutoff rh V ⊆ positiveCutoff rh T := cutoff_mono rh hVT
  have hdiff : (∑ j ∈ positiveCutoff rh T \ positiveCutoff rh V, p j) =
      (∑ j ∈ positiveCutoff rh T, p j) - ∑ j ∈ positiveCutoff rh V, p j :=
    eq_sub_of_add_eq (Finset.sum_sdiff hcut (f := p))
  refine hL T hLT t ?_
  change ‖∑ j ∈ positiveCutoff rh T \ positiveCutoff rh V, p j‖ ≤ _
  rw [hdiff]
  calc
    _ ≤ ‖∑ j ∈ positiveCutoff rh T, p j‖ + ‖∑ j ∈ positiveCutoff rh V, p j‖ :=
      norm_sub_le _ _
    _ ≤ ε * (T * Real.log T) + ε * (T * Real.log T) :=
      add_le_add (hTsmall t hlo hTupper) hVb
    _ = _ := by dsimp [ε]; ring

/-- At positive critical resolution, the uniform upper pair-correlation bound
suffices for the Gaussian hard-band limit of actual harmonic zeta collisions. -/
theorem harmonic_zeta_critical_collision_limit (rh : RiemannHypothesis)
    (hcorr : MontgomeryUpperBoundOnLogBands (zetaSpectrum rh))
    (T η : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hresolution : ∃ a > (0 : ℝ), ∀ᶠ n in atTop, a ≤ η n * Real.log (T n)) :
    let scale (n : ℕ) := Real.sqrt ((n : ℝ) * pairMoment
      (fun j : ↥(positiveCutoff rh (T n)) => ordinate j.1)
      (fun j => harmonicWeight j.1 / harmonicMass rh (T n)) 2 / 2)
    Tendsto (fun n : ℕ => η n / scale n) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => scale n *
      tailCollisionMass (fun j : ↥(positiveCutoff rh (T n)) => ordinate j.1)
        (fun j => harmonicWeight j.1) n (η n) /
        (η n * harmonicMass rh (T n)^(2*n))) atTop (𝓝 (1 / Real.sqrt Real.pi)) :=
  harmonic_zeta_critical_collision_limit_of_long_deficit rh (fun A hA =>
    ⟨1 / 32, by positivity, by simpa only [div_div] using harmonic_long_deficit rh hcorr A hA⟩)
    T η hT hη hh hresolution

#print axioms harmonic_zeta_critical_collision_limit

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalResolutionCollisionLimit
