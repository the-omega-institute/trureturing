/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform upper pair-correlation bound yields the harmonic zeta collision limit at critical resolution. -/

import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.OmittedSpectrumCutoff
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
import D5.S3.Weil.ZetaExplicit.LandauUniformCutoff

/-! The Lorentzian pair sum controls the height of each finite phase peak.
A long-band upper bound therefore extends the collision limit to resolutions
with an eventual positive lower bound on the product of resolution and log-height. -/

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalResolutionCollisionLimit

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
  (harmonic_band_transfer)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
  (harmonicOrdinate harmonicProbability)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
  (harmonicScale harmonic_central_window_limit harmonic_multiple_log_annulus_limit
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
open D5.S3.Weil.ZetaExplicit.LandauUniformCutoff (actual_cutoff_landau_envelope)
open Finset
open D5.S3.Fourier.Concentration.FejerCollisionSecants (rampCollisionMass)

private theorem peak_cube_le_energy
    (f : ℝ → ℝ) (M Y : ℝ) (hM : 0 < M) (hY : 1 ≤ Y)
    (hf : Continuous f) (h0 : ∀ u, 0 ≤ f u) (hbound : f 0 ≤ M)
    (hchange : ∀ u, f 0 - f u ≤ Y * M * |u|)
    (hi : Integrable (fun u : ℝ => Real.exp (-2 * |u|) * f u ^ 2)) :
    f 0 ^ 3 ≤ (4 * Real.exp 1 * Y * M) *
      ∫ u : ℝ, Real.exp (-2 * |u|) * f u ^ 2 := by
  let F (u : ℝ) := Real.exp (-2 * |u|) * f u ^ 2
  let r : ℝ := f 0 / (2 * Y * M)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hden : 0 < 2 * Y * M := by positivity
  have hr : 0 ≤ r := div_nonneg (h0 0) hden.le
  have heq : 2 * Y * M * r = f 0 := by dsimp [r]; field_simp
  have hrmax : r ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).2
    calc
      f 0 ≤ M := hbound
      _ ≤ 1 / 2 * (2 * Y * M) := by nlinarith [mul_le_mul_of_nonneg_right hY hM.le]
  have hordered : -r ≤ r := by linarith
  have hpoint (u : ℝ) (hu : u ∈ Icc (-r) r) :
      Real.exp (-1) * (f 0 / 2) ^ 2 ≤ F u := by
    have hua : |u| ≤ r := abs_le.mpr hu
    have hexp : Real.exp (-1) ≤ Real.exp (-2 * |u|) :=
      Real.exp_le_exp.mpr (by linarith)
    have hfl : f 0 / 2 ≤ f u := by
      have hm := mul_le_mul_of_nonneg_left hua (show 0 ≤ Y * M by positivity)
      nlinarith only [hchange u, hm, heq]
    exact mul_le_mul hexp
      (pow_le_pow_left₀ (div_nonneg (h0 0) (by norm_num)) hfl 2)
      (by positivity) (by positivity)
  have hlocal : (∫ _ in -r..r, Real.exp (-1) * (f 0 / 2) ^ 2) ≤
      (∫ u in -r..r, F u) := by
    apply intervalIntegral.integral_mono_on hordered
      (continuous_const.intervalIntegrable _ _)
      ((by unfold F; fun_prop : Continuous F).intervalIntegrable _ _) hpoint
  have hglobal : (∫ u in -r..r, F u) ≤ ∫ u : ℝ, F u := by
    rw [intervalIntegral.integral_of_le hordered]
    exact setIntegral_le_integral hi (ae_of_all _ fun u => by unfold F; positivity)
  have hmass := hlocal.trans hglobal
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add] at hmass
  have hc : 0 ≤ 4 * Real.exp 1 * Y * M := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmass hc
  have hinv : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hnormalize :
      (4 * Real.exp 1 * Y * M) * ((r+r) * (Real.exp (-1) * (f 0 / 2) ^ 2)) = f 0 ^ 3 := by
    calc
      _ = (Real.exp 1 * Real.exp (-1)) * (2 * Y * M * r) * f 0 ^ 2 := by ring
      _ = _ := by rw [hinv, heq]; ring
  simpa only [hnormalize, F] using hscaled

private lemma phase_change (g t u : ℝ) :
    ‖phase g t - phase g (t - u)‖ ≤ |g| * |u| := by
  simpa only [phase, sub_sub_cancel, mul_comm, mul_left_comm, mul_assoc] using
    (unit_phase_diff g t (t - u))

private theorem score_cube_le_energy {J : Type*} [Fintype J]
    (g w : J → ℝ) (Y t : ℝ) (hY : 1 ≤ Y)
    (hg : ∀ j, |g j| ≤ Y) (hw : ∀ j, 0 ≤ w j)
    (hi : Integrable (fun u : ℝ =>
      Real.exp (-2 * |u|) * ‖complexScore g w (t-u)‖ ^ 2)) :
    ‖complexScore g w t‖ ^ 3 ≤ (4 * Real.exp 1 * Y * (∑ j, w j)) *
      ∫ u : ℝ, Real.exp (-2 * |u|) * ‖complexScore g w (t-u)‖ ^ 2 := by
  classical
  let M := ∑ j, w j
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => hw j
  have hbound (v : ℝ) : ‖complexScore g w v‖ ≤ M := by
    unfold complexScore M
    calc
      _ ≤ ∑ j, ‖(w j : ℂ) * phase (g j) v‖ := norm_sum_le _ _
      _ = _ := by simp [norm_phase, Complex.norm_real, abs_of_nonneg, hw]
  rcases hM.eq_or_lt with hM | hM
  · have hz : ‖complexScore g w t‖ = 0 :=
      le_antisymm ((hbound t).trans hM.ge) (norm_nonneg _)
    change ‖complexScore g w t‖ ^ 3 ≤ (4 * Real.exp 1 * Y * M) * _
    simp [← hM, hz]
  · let f (u : ℝ) := ‖complexScore g w (t - u)‖
    have hf : Continuous f :=
      ((complexScore_continuous g w).comp (continuous_const.sub continuous_id)).norm
    have hshift (u : ℝ) : f 0 - f u ≤ Y * M * |u| := by
      have hn := norm_sub_norm_le (complexScore g w t) (complexScore g w (t-u))
      simp only [f, sub_zero]
      refine hn.trans ?_
      unfold complexScore
      rw [← Finset.sum_sub_distrib]
      simp only [← mul_sub]
      calc
        _ ≤ ∑ j, ‖(w j : ℂ) * (phase (g j) t - phase (g j) (t-u))‖ := norm_sum_le _ _
        _ ≤ ∑ j, w j * (Y * |u|) := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
          exact mul_le_mul_of_nonneg_left
            ((phase_change (g j) t u).trans
              (mul_le_mul_of_nonneg_right (hg j) (abs_nonneg u))) (hw j)
        _ = _ := by rw [← Finset.sum_mul]; ring
    simpa [f, sub_zero, M] using
      (peak_cube_le_energy f M Y hM hY hf (fun _ => norm_nonneg _) (by simpa [f] using hbound t)
        hshift hi)

private theorem energy_eq_cos_sum {J : Type*} [Fintype J]
    (g w : J → ℝ) (t : ℝ) :
    (∫ u : ℝ, exponentialWeight u * ‖complexScore g w (t-u)‖ ^ 2) =
      ∑ j, ∑ k, (w j * w k) *
        ((4 / (4 + (g j - g k) ^ 2)) * Real.cos ((g j - g k) * t)) := by
  have hi (j k : J) :
      Integrable (fun u : ℝ => (w j * w k) *
        (exponentialWeight u * Real.cos ((g j - g k) * (t - u)))) :=
    (exponentialWeight_mul_cos_integrable _ _).const_mul _
  simp_rw [score_square_cosine g w, Finset.mul_sum,
    show ∀ a b c : ℝ, a * (b * c) = b * (a * c) from fun a b c => by ring]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k), integral_const_mul, exponentialWeight_cosine]

private theorem cutoff_cube_le_montgomery (S : Spectrum) {Y : ℝ} (hY : 1 < Y) (t : ℝ) :
    ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖ ^ 3 ≤
      (4 * Real.exp 1 * Y * S.N Y) *
        (Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y) := by
  classical
  let J := ↥(S.cut Y)
  let g (j : J) := S.gamma j.1
  let w (j : J) : ℝ := S.mult j.1
  have hg (j : J) : |g j| ≤ Y := by
    rw [abs_of_pos (S.gamma_pos j.1)]
    exact (S.finite_le Y).mem_toFinset.mp j.2
  have hw (j : J) : 0 ≤ w j := Nat.cast_nonneg _
  have hbound (u : ℝ) : ‖complexScore g w (t-u)‖ ≤ ∑ j, w j := by
    unfold complexScore
    calc
      _ ≤ ∑ j, ‖(w j : ℂ) * phase (g j) (t-u)‖ := norm_sum_le _ _
      _ = _ := by simp [norm_phase, Complex.norm_real, abs_of_nonneg, hw]
  have hi : Integrable (fun u : ℝ => exponentialWeight u * ‖complexScore g w (t-u)‖ ^ 2) := by
    refine exponentialWeight_integrable.mul_bdd (c := (∑ j, w j)^2) ?_
      (ae_of_all _ fun u => ?_)
    · exact (((complexScore_continuous g w).comp
        (continuous_const.sub continuous_id)).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound u) 2
  have hsum : complexScore g w t =
      ∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t := by
    unfold complexScore
    exact Finset.sum_coe_sort (S.cut Y) (fun j => (S.mult j : ℂ) * phase (S.gamma j) t)
  have hmass : (∑ j, w j) = (S.N Y : ℝ) := by
    rw [Spectrum.N, Nat.cast_sum]
    exact Finset.sum_coe_sort (S.cut Y) (fun j => (S.mult j : ℝ))
  have hpair := energy_eq_cos_sum g w t
  rw [← montgomery_normalization S hY t]
  rw [← hsum, ← hmass]
  have hc := score_cube_le_energy g w Y t hY.le hg hw hi
  change _ ≤ (4 * Real.exp 1 * Y * ∑ j, w j) * (∫ u : ℝ, exponentialWeight u * ‖complexScore g w (t-u)‖ ^ 2) at hc
  rw [hpair] at hc
  refine hc.trans_eq ?_
  congr 1
  change (∑ j : ↥(S.cut Y), ∑ k : ↥(S.cut Y), (S.mult j.1 : ℝ) * S.mult k.1 *
      ((4 / (4 + (S.gamma j.1 - S.gamma k.1) ^ 2)) *
        Real.cos ((S.gamma j.1 - S.gamma k.1) * t))) = _
  rw [Finset.sum_coe_sort (S.cut Y) (fun j =>
    ∑ k : ↥(S.cut Y), (S.mult j : ℝ) * S.mult k.1 *
      ((4 / (4 + (S.gamma j - S.gamma k.1) ^ 2)) *
        Real.cos ((S.gamma j - S.gamma k.1) * t)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_coe_sort (S.cut Y) (fun k => (S.mult j : ℝ) * S.mult k *
    ((4 / (4 + (S.gamma j - S.gamma k) ^ 2)) * Real.cos ((S.gamma j - S.gamma k) * t)))]
  apply Finset.sum_congr rfl
  intro k _
  unfold pairCos
  ring

private theorem cutoff_small_of_pair_bound (S : Spectrum) (hN : CountAsymptotic S)
    (A : ℝ)
    (hcorr : ∀ ε > (0 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        montgomery S (t / Real.log Y) Y ≤ ε * Real.log Y) :
    ∀ ε > (0 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖ ≤
          ε * (Y * Real.log Y) := by
  intro ε hε
  obtain ⟨C, hC, hcount⟩ := count_upper S hN
  let A₀ := 4 * Real.exp 1 * C / (2 * Real.pi)
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  let δ := ε ^ 3 / A₀
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ), hcount, hcorr δ hδ] with Y hY hcnt hcorrY
  intro t htl htu
  let F := montgomery S (t / Real.log Y) Y
  have hF : 0 ≤ δ * Real.log Y := by have := Real.log_pos hY; positivity
  have hg := cutoff_cube_le_montgomery S hY t
  have hlog := Real.log_pos hY
  have hYpos : 0 < Y := zero_lt_one.trans hY
  have hδeq : A₀ * δ = ε ^ 3 := by dsimp [δ]; field_simp
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 3 ≠ 0)).1 ?_
  calc
    _ ≤ (4 * Real.exp 1 * Y * S.N Y) * (Y * Real.log Y / (2 * Real.pi) * F) := hg
    _ ≤ (4 * Real.exp 1 * Y * S.N Y) * (Y * Real.log Y / (2 * Real.pi) * (δ * Real.log Y)) := by
      gcongr
      exact hcorrY t htl htu
    _ ≤ (4 * Real.exp 1 * Y * (C * (Y * Real.log Y))) *
        (Y * Real.log Y / (2 * Real.pi) * (δ * Real.log Y)) := by gcongr
    _ = (A₀ * δ) * (Y * Real.log Y)^3 := by dsimp [A₀]; ring
    _ = _ := by rw [hδeq]; ring

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

private theorem critical_window_deficit (rh : RiemannHypothesis)
    (hcorr : MontgomeryUpperBoundOnLogBands (zetaSpectrum rh)) (A : ℝ) (hA : 1 < A) :
    ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, 1 / H ≤ |t| → |t| ≤ A * Real.log H →
      1 / (1048576 * Real.log H) ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖ := by
  obtain ⟨C,hC,henv⟩ := actual_cutoff_landau_envelope rh
  have h₁ := whole_log_window_deficit rh C hC (fun V t hV ht => by
    refine (henv V t hV ht).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have hnonneg : 0 ≤ Real.exp (|t| / 2) * (1 + Real.log V) := by
      have := Real.log_nonneg hV.le
      positivity
    linarith)
  have h₂ := harmonic_long_deficit rh hcorr A hA
  filter_upwards [h₁, h₂, eventually_gt_atTop (1 : ℝ)] with H hshort hlong hH
  intro t hlo hhi
  by_cases hb : |t| ≤ Real.log H
  · exact hshort t hlo hb
  · exact (div_le_div_of_nonneg_left zero_le_one (mul_pos (by norm_num) (Real.log_pos hH))
        (mul_le_mul_of_nonneg_right (by norm_num) (Real.log_pos hH).le)).trans
      (hlong t (le_of_not_ge hb) hhi)

private theorem tendsto_of_relative_windows {F : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (happrox : ∀ ε > (0 : ℝ), ∃ I : ℕ → ℝ, Tendsto I atTop (𝓝 c) ∧
      ∀ᶠ n in atTop, I n ≤ F n ∧ F n - I n ≤ ε * F n) :
    Tendsto F atTop (𝓝 c) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    obtain ⟨I, hI, hle⟩ := happrox 1 one_pos
    filter_upwards [hI.eventually (eventually_gt_nhds hx), hle] with n hi hl
    exact hi.trans_le hl.1
  · intro y hy
    have hypos := hc.trans_lt hy
    let ε := (y - c) / (2 * y)
    have hε : 0 < ε := div_pos (sub_pos.mpr hy) (by positivity)
    have hεeq : ε * y = (y - c) / 2 := by dsimp [ε]; field_simp
    have hε1 : ε < 1 := by
      apply (mul_lt_mul_iff_of_pos_right hypos).mp
      rw [hεeq, one_mul]
      linarith
    obtain ⟨I, hI, hle⟩ := happrox ε hε
    have hmid : c < (c + y) / 2 := by linarith
    filter_upwards [hI.eventually (eventually_lt_nhds hmid), hle] with n hi hl
    by_contra! hcase
    have hscaled := mul_le_mul_of_nonneg_left hcase (sub_nonneg.mpr hε1.le)
    nlinarith only [hi, hl.2, hscaled, hεeq]

private theorem critical_harmonic_full_fejer_limit (rh : RiemannHypothesis)
    (hcorr : MontgomeryUpperBoundOnLogBands (zetaSpectrum rh)) (T η : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hr : Tendsto (fun n : ℕ => η n / harmonicScale rh T n) atTop (𝓝 0))
    (hresolution : ∃ a > (0 : ℝ), ∀ᶠ n in atTop, a ≤ η n * Real.log (T n)) :
    Tendsto (fun n : ℕ => harmonicScale rh T n / η n *
      ∫ t : ℝ, K (η n) t *
        ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n))
      atTop (𝓝 (1 / (2 * Real.sqrt Real.pi))) := by
  classical
  let F (n : ℕ) (t : ℝ) := K (η n) t *
    ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n)
  let s := harmonicScale rh T
  change Tendsto (fun n => s n / η n * ∫ t : ℝ, F n t)
    atTop (𝓝 (1 / (2 * Real.sqrt Real.pi)))
  obtain ⟨a, ha, haη⟩ := hresolution
  apply tendsto_of_relative_windows (by positivity)
  intro ε hε
  let A := 2 + max (1 / a) (64 / (a * ε))
  have hA : 1 < A := by
    dsimp [A]
    have h := (one_div_pos.mpr ha).trans_le (le_max_left (1 / a) (64 / (a * ε)))
    linarith
  let I (n : ℕ) := s n / η n * (∫ t in -(A * Real.log (T n))..A * Real.log (T n), F n t)
  have hψ := harmonic_central_window_limit rh T η hT hη hh hr
  have hz := harmonic_multiple_log_annulus_limit rh T η A hA.le hT hη hh
    (critical_window_deficit rh hcorr A hA)
  refine ⟨I, ?_, ?_⟩
  · simpa only [add_zero] using (hψ.add hz).congr (fun n : ℕ => by dsimp [F, I, s]; ring)
  · filter_upwards [haη, hη, hT.eventually_gt_atTop 1, hT.eventually (harmonic_pair_bounds rh)] with
      n hηlog hηn hTn hpair
    let R := A * Real.log (T n)
    have hRpos : 0 < R := mul_pos (zero_lt_one.trans hA) (Real.log_pos hTn)
    have hAl : 1 / a ≤ A := by
      dsimp [A]
      linarith [le_max_left (1 / a) (64 / (a * ε))]
    have hAr : 64 / (a * ε) ≤ A := by
      dsimp [A]
      linarith [le_max_right (1 / a) (64 / (a * ε))]
    have hpos : 0 < A := zero_lt_one.trans hA
    have haR : a * A ≤ η n * R := by
      dsimp [R]
      nlinarith only [mul_le_mul_of_nonneg_right hηlog hpos.le]
    have hR : 1 ≤ η n * R := by
      have hl := (div_le_iff₀ ha).1 hAl
      linarith only [hl, haR]
    have hcoef : 64 / (η n * R) ≤ ε := by
      have hu := (div_le_iff₀ (mul_pos ha hε)).1 hAr
      apply (div_le_iff₀ (mul_pos hηn hRpos)).2
      nlinarith only [hu, mul_le_mul_of_nonneg_left haR hε.le]
    have hrel := harmonic_fejer_relative_control rh T η hηn hR hpair.2.1
    have hwhole : 0 ≤ s n / η n * ∫ t : ℝ, F n t := by
      exact mul_nonneg (by dsimp [s, harmonicScale]; positivity)
        (integral_nonneg fun t => mul_nonneg ((fejer_law hηn).1 t) (by positivity))
    exact ⟨hrel.1, hrel.2.trans (mul_le_mul_of_nonneg_right hcoef hwhole)⟩

private theorem normalized_critical_harmonic_collision_limit (rh : RiemannHypothesis)
    (hcorr : MontgomeryUpperBoundOnLogBands (zetaSpectrum rh)) (T η : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hr : Tendsto (fun n : ℕ => η n / harmonicScale rh T n) atTop (𝓝 0))
    (hresolution : ∃ a > (0 : ℝ), ∀ᶠ n in atTop, a ≤ η n * Real.log (T n)) :
    Tendsto (fun n : ℕ => harmonicScale rh T n / η n *
      tailCollisionMass (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) n (η n))
      atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  apply normalized_harmonic_collision_limit_of_fejer rh T η hT hη
  intro x hx
  let ε (n : ℕ) := x * η n
  have hε : ∀ᶠ n : ℕ in atTop, 0 < ε n := hη.mono fun _ he => mul_pos hx he
  have hεr : Tendsto (fun n : ℕ => ε n / harmonicScale rh T n) atTop (𝓝 0) := by
    simpa only [ε, mul_div_assoc, mul_zero] using hr.const_mul x
  have hεresolution : ∃ a > (0 : ℝ), ∀ᶠ n in atTop, a ≤ ε n * Real.log (T n) := by
    obtain ⟨a, ha, hbound⟩ := hresolution
    refine ⟨x*a, mul_pos hx ha, hbound.mono ?_⟩
    intro n hn
    simpa only [ε, mul_assoc] using mul_le_mul_of_nonneg_left hn hx.le
  exact critical_harmonic_full_fejer_limit rh hcorr T ε hT hε hh hεr hεresolution

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
        (η n * harmonicMass rh (T n)^(2*n))) atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  intro scale hr
  apply (normalized_critical_harmonic_collision_limit rh hcorr T η hT hη hh hr hresolution).congr'
  filter_upwards with n
  unfold harmonicProbability
  rw [normalized_collision_eq_div_mass]
  rw [div_mul_div_comm]
  rfl

#print axioms harmonic_zeta_critical_collision_limit

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalResolutionCollisionLimit
