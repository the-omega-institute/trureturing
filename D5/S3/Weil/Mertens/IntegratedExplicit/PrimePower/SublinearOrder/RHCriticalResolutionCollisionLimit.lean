/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalResolutionCollisionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform upper pair-correlation bound yields the harmonic zeta collision limit at critical resolution. -/

import D5.S3.Analytic.Oscillation.MontgomeryWindow
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
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (score_conj)
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
  (harmonicScale centralIntegral_scale annulusIntegral_le logarithmic_window_decay
    score_power_le_exp whole_log_window_deficit ramp_eq_fejer normalized_collision_eq_div_mass)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Fourier.Concentration.FejerRelativeLocalization
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Fourier.Concentration.FejerCollisionLimit
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
open D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
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
  have hphase : phase g t = phase g (t - u) * Complex.exp (Complex.I * ((g * u : ℝ) : ℂ)) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hphase, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := g * u))

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

private theorem square_eq_cos_sum {J : Type*} [Fintype J]
    (g w : J → ℝ) (t : ℝ) :
    ‖complexScore g w t‖ ^ 2 =
      ∑ j, ∑ k, w j * w k * Real.cos ((g j - g k) * t) := by
  have hprod :
      complexScore g w t * star (complexScore g w t) =
        ∑ j, ∑ k, ((w j * w k : ℝ) : ℂ) * phase (g j - g k) t := by
    rw [score_conj]
    unfold complexScore
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [sub_eq_add_neg, character_add, Complex.ofReal_mul]
    ring
  change complexScore g w t * (starRingEnd ℂ (complexScore g w t)) = _ at hprod
  rw [Complex.mul_conj'] at hprod
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum,
    Complex.re_ofReal_mul, phase_re] using
    congrArg Complex.re hprod

private theorem energy_eq_cos_sum {J : Type*} [Fintype J]
    (g w : J → ℝ) (t : ℝ) :
    (∫ u : ℝ, exponentialWeight u * ‖complexScore g w (t-u)‖ ^ 2) =
      ∑ j, ∑ k, (w j * w k) *
        ((4 / (4 + (g j - g k) ^ 2)) * Real.cos ((g j - g k) * t)) := by
  have hi (j k : J) :
      Integrable (fun u : ℝ => (w j * w k) *
        (exponentialWeight u * Real.cos ((g j - g k) * (t - u)))) :=
    (exponentialWeight_mul_cos_integrable _ _).const_mul _
  simp_rw [square_eq_cos_sum g w, Finset.mul_sum,
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

private theorem harmonic_central_window_limit (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hr : Tendsto (fun n : ℕ => η n / harmonicScale rh T n) atTop (𝓝 0))
    :
    Tendsto (fun n : ℕ => harmonicScale rh T n / η n *
      ∫ t in -(1 / T n)..1 / T n, K (η n) t *
        ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n))
      atTop (𝓝 (1 / (2 * Real.sqrt Real.pi))) := by
  let g (n : ℕ) := harmonicOrdinate rh (T n)
  let w (n : ℕ) := harmonicProbability rh (T n)
  let P (n k : ℕ) := pairMoment (g n) (w n) k
  let s := harmonicScale rh T
  let A (n : ℕ) := s n / T n
  have hlog := Real.tendsto_log_atTop.comp hT
  have hn : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
    (eventually_gt_atTop (0 : ℕ)).mono fun n h => by exact_mod_cast h
  have hPair := hT.eventually (harmonic_pair_bounds rh)
  have hw : ∀ᶠ n : ℕ in atTop, ∀ j, 0 ≤ w n j :=
    hPair.mono fun _ h => h.2.1
  have hw1 : ∀ᶠ n : ℕ in atTop, ∑ j, w n j = 1 :=
    hPair.mono fun _ h => h.2.2.1
  have hM : ∀ᶠ n : ℕ in atTop, 0 < P n 2 := by
    filter_upwards [hPair, hT.eventually_gt_atTop 1] with n hp hTn
    exact (div_pos (sq_pos_of_pos (zero_lt_one.trans hTn))
      (mul_pos (by norm_num) (Real.log_pos hTn))).trans_le hp.2.2.2.2.2.1
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < s n ∧ s n ^ 2 = (n : ℝ) * P n 2 / 2 := by
    filter_upwards [hn, hM] with n hn hP
    refine ⟨Real.sqrt_pos.2 ?_, Real.sq_sqrt ?_⟩ <;> positivity
  have hA : Tendsto A atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    let B' := max 1 B
    have hB : 0 < B' := zero_lt_one.trans_le (le_max_left _ _)
    have hE : 0 < 1 / (8192 * B'^2) := by positivity
    filter_upwards [hT.eventually_gt_atTop 1, hlog.eventually_ge_atTop 1, hn, hPair, hscale,
      hh.eventually_lt_const hE] with n hTn hLog hn hPair hs hq
    have hTpos := zero_lt_one.trans hTn
    change 1 ≤ Real.log (T n) at hLog
    have hLogpos := zero_lt_one.trans_le hLog
    have hq' : (8192 * B'^2) * Real.log (T n)^2 ≤ (n : ℝ) := by
      have h := (div_lt_iff₀ hn).1 hq
      rw [one_div, inv_mul_eq_div] at h
      have hh := (lt_div_iff₀ (by positivity : 0 < 8192 * B'^2)).1 h
      simpa only [mul_comm (Real.log (T n)^2)] using hh.le
    have hlogSq : Real.log (T n) ≤ Real.log (T n)^2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hLog) hLogpos.le]
    have hq'' := (mul_le_mul_of_nonneg_left hlogSq
      (show 0 ≤ 8192 * B'^2 by positivity)).trans hq'
    have hLow : (T n)^2 / (4096 * Real.log (T n)) ≤ P n 2 := hPair.2.2.2.2.2.1
    have hLow' := (div_le_iff₀ (by positivity : 0 < 4096 * Real.log (T n))).1 hLow
    have hp := mul_le_mul_of_nonneg_left hq'' (show 0 ≤ P n 2 from
      ((div_nonneg (sq_nonneg _) (by positivity)).trans hLow))
    have hb := mul_le_mul_of_nonneg_left hLow' (show 0 ≤ B'^2 from sq_nonneg _)
    have hs' : (B' * T n)^2 ≤ s n ^ 2 := by
      rw [hs.2, mul_pow]
      nlinarith only [hp, hb]
    exact (le_max_right 1 B).trans ((le_div_iff₀ hTpos).2
      ((sq_le_sq₀ (mul_nonneg hB.le hTpos.le) hs.1.le).1 hs'))
  have hwin : ∀ᶠ n : ℕ in atTop, A n ^ 2 * P n 4 ≤ 6 * (n : ℝ) * P n 2 ^ 2 := by
    filter_upwards [hT.eventually_gt_atTop 1, hn, hPair, hscale] with n hTn hn hp hs
    have hb : P n 4 ≤ (T n)^2 * P n 2 := hp.2.2.2.2.2.2
    calc
      A n ^ 2 * P n 4 ≤ A n ^ 2 * ((T n)^2 * P n 2) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = s n ^ 2 * P n 2 := by dsimp [A]; field_simp
      _ ≤ _ := by
        rw [hs.2]
        nlinarith only [mul_nonneg hn.le (sq_nonneg (P n 2))]
  have hcenter := central_fejer_gaussian_limit g w
    (hw.mono fun _ hn i j => mul_nonneg (hn i) (hn j)) hw1 hM
    (fun n : ℕ => η n / s n) A hr hA hwin
  apply hcenter.congr'
  filter_upwards [hscale, hη, hT.eventually_gt_atTop 1] with n hs he hTn
  have hEq : A n / s n = 1 / T n := by dsimp [A]; field_simp [hs.1.ne']
  have hsc := (centralIntegral_scale (g n) (w n) n (A := A n) hs.1 he).symm
  rw [hEq] at hsc
  exact hsc

private theorem harmonic_multiple_log_annulus_limit (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (B : ℝ) (hB : 1 < B)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hd : ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, 1 / H ≤ |t| → |t| ≤ B * Real.log H →
      1 / (1048576 * Real.log H) ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖) :
    let F (n : ℕ) (t : ℝ) := K (η n) t *
      ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n)
    Tendsto (fun n : ℕ => harmonicScale rh T n / η n *
      ((∫ t in -(B * Real.log (T n))..B * Real.log (T n), F n t) -
      (∫ t in -(1 / T n)..1 / T n, F n t))) atTop (𝓝 0) := by
  intro F
  let c : ℝ := 1 / 1048576
  have hc : 0 < c := by norm_num [c]
  have hdecay := (logarithmic_window_decay T hT hh hc).div_const Real.pi
  rw [zero_div] at hdecay
  have hdecay := hdecay.const_mul B
  rw [mul_zero] at hdecay
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
  · filter_upwards [hη, hT.eventually_ge_atTop (Real.exp 1)] with n hηn hTn
    have hTpos : 0 < T n := (Real.exp_pos _).trans_le hTn
    have hTL : 1 ≤ Real.log (T n) := by
      simpa using Real.log_le_log (Real.exp_pos 1) hTn
    have hwin₀ : 1 / T n ≤ Real.log (T n) :=
      ((div_le_one hTpos).2 (Real.one_le_exp_iff.2 zero_le_one |>.trans hTn)).trans hTL
    have hwin : 1 / T n ≤ B * Real.log (T n) := hwin₀.trans (by
      nlinarith only [mul_nonneg (show 0 ≤ B-1 by linarith) (show 0 ≤ Real.log (T n) by linarith)])
    have hf : Continuous (F n) :=
      (K_continuous _).mul ((complexScore_continuous _ _).norm.pow _)
    have hF0 (t : ℝ) : 0 ≤ F n t := mul_nonneg ((fejer_law hηn).1 t) (by positivity)
    apply mul_nonneg (by dsimp [harmonicScale]; positivity)
    apply sub_nonneg.2
    exact intervalIntegral.integral_mono_interval (neg_le_neg hwin)
      (by linarith [one_div_pos.mpr hTpos]) hwin (ae_of_all _ hF0) (hf.intervalIntegrable _ _)
  · filter_upwards [hη, hT.eventually hd, hT.eventually (harmonic_pair_bounds rh),
      hT.eventually_ge_atTop (Real.exp 1)] with n hηn hdn hpair hTn
    have hTpos : 0 < T n := (Real.exp_pos _).trans_le hTn
    have hTL : 1 ≤ Real.log (T n) := by
      simpa using Real.log_le_log (Real.exp_pos 1) hTn
    have hwin₀ : 1 / T n ≤ Real.log (T n) :=
      ((div_le_one hTpos).2 (Real.one_le_exp_iff.2 zero_le_one |>.trans hTn)).trans hTL
    have hwin : 1 / T n ≤ B * Real.log (T n) := hwin₀.trans (by
      nlinarith only [mul_nonneg (show 0 ≤ B-1 by linarith) (show 0 ≤ Real.log (T n) by linarith)])
    obtain ⟨_, hw, hw1, _, _, _, _⟩ := hpair
    change (∑ j, harmonicProbability rh (T n) j) = 1 at hw1
    let m := pairMoment (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) 2
    have hm2 : m ≤ (T n)^2 := by
      change ∑ i, ∑ j, harmonicProbability rh (T n) i * harmonicProbability rh (T n) j *
        (ordinate i.1 - ordinate j.1) ^ 2 ≤ (T n)^2
      have hsp (j : ↥(positiveCutoff rh (T n))) : 0 < ordinate j.1 ∧ ordinate j.1 ≤ T n :=
        ⟨j.1.property.2, (cutoff_mem rh _ _).1 j.2⟩
      calc
        _ ≤ ∑ i, ∑ j, harmonicProbability rh (T n) i * harmonicProbability rh (T n) j *
            (T n)^2 := by
          refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i) (hw j))
          apply sq_le_sq.mpr
          rw [abs_of_pos hTpos]
          exact abs_le.2 ⟨by linarith [(hsp i).1, (hsp j).2], by linarith [(hsp j).1, (hsp i).2]⟩
        _ = _ := by
          simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
          change (∑ j, harmonicProbability rh (T n) j) *
            ((∑ j, harmonicProbability rh (T n) j) * (T n)^2) = _
          rw [hw1, one_mul, one_mul]
    have hscale : harmonicScale rh T n ≤ Real.sqrt (n : ℝ) * T n := by
      unfold harmonicScale
      have hs := Real.sqrt_le_sqrt (show (n : ℝ) * m / 2 ≤ (n : ℝ) * (T n)^2 from by
        nlinarith only [mul_le_mul_of_nonneg_left hm2 (Nat.cast_nonneg n),
          mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg (T n))])
      simpa only [Real.sqrt_mul (Nat.cast_nonneg n : (0 : ℝ) ≤ n), Real.sqrt_sq hTpos.le] using hs
    let E := Real.exp (-(2 * c * (n : ℝ) / Real.log (T n)))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hf : Continuous (F n) :=
      (K_continuous _).mul ((complexScore_continuous _ _).norm.pow _)
    have hann := annulusIntegral_le (F n) hf (one_div_pos.mpr hTpos).le hwin
      (D := η n / (2 * Real.pi) * E) (fun t hlo hhi => by
        apply mul_le_mul (K_cap hηn t) _ (by positivity) (by positivity)
        have h := score_power_le_exp _ _ (norm_nonneg _) (hdn t hlo hhi) n
        convert h using 2
        dsimp [E, c]
        ring)
    have hr : 0 ≤ harmonicScale rh T n / η n := by dsimp [harmonicScale]; positivity
    calc
      _ ≤ harmonicScale rh T n / η n * (2 * (B * Real.log (T n) - 1 / T n) *
          (η n / (2 * Real.pi) * E)) := mul_le_mul_of_nonneg_left hann hr
      _ = harmonicScale rh T n * (B * Real.log (T n) - 1 / T n) * E / Real.pi := by
        field_simp [hηn.ne', Real.pi_ne_zero]
      _ ≤ (Real.sqrt (n : ℝ) * T n * (B * Real.log (T n)) * E) / Real.pi := by
        apply div_le_div_of_nonneg_right _ Real.pi_pos.le
        apply mul_le_mul_of_nonneg_right _ hE
        refine mul_le_mul hscale (by linarith [one_div_pos.mpr hTpos]) (sub_nonneg.mpr hwin) ?_
        exact mul_nonneg (Real.sqrt_nonneg _) hTpos.le
      _ = B * (Real.sqrt (n : ℝ) * T n * Real.log (T n) * E / Real.pi) := by ring

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
  have hz := harmonic_multiple_log_annulus_limit rh T η A hA hT hη hh
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
    have hg : Integrable (F n) := by
      dsimp [F]
      simp_rw [moment_eq_pair]
      exact kernel_pair_integrable _ _ _ hηn
    have hn : ∀ t, 0 ≤ F n t := fun t => mul_nonneg ((fejer_law hηn).1 t) (by positivity)
    have hleft : (∫ t in -R..R, F n t) ≤ ∫ t : ℝ, F n t := by
      rw [intervalIntegral.integral_of_le (by linarith [hRpos])]
      exact setIntegral_le_integral hg (ae_of_all _ hn)
    have hscale : 0 ≤ s n / η n := by dsimp [s, harmonicScale]; positivity
    have he := relative_fejer_truncation (harmonicOrdinate rh (T n))
      (harmonicProbability rh (T n)) hpair.2.1 n hηn hR
    change (∫ t : ℝ, F n t) - (∫ t in -R..R, F n t) ≤
      (64 / (η n * R)) * ∫ t : ℝ, F n t at he
    have hright := he.trans (mul_le_mul_of_nonneg_right hcoef
      (integral_nonneg hn))
    refine ⟨mul_le_mul_of_nonneg_left hleft hscale, ?_⟩
    dsimp only [I]
    rw [← mul_sub]
    convert mul_le_mul_of_nonneg_left hright hscale using 1; ring

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
  let s := harmonicScale rh T
  let g (n : ℕ) := harmonicOrdinate rh (T n)
  let w (n : ℕ) := harmonicProbability rh (T n)
  let S (n : ℕ) := piAntidiag (univ : Finset ↥(positiveCutoff rh (T n))) n
  let X (n : ℕ) := monomialFrequency (g n)
  let W (n : ℕ) := monomialWeight (w n)
  let B (n : ℕ) := s n / η n ^ 2
  let c := 1 / (2 * Real.sqrt Real.pi)
  have hB : ∀ᶠ n : ℕ in atTop, 0 ≤ B n := by
    filter_upwards with n
    dsimp [B, s, harmonicScale]
    positivity
  have hw : ∀ᶠ n : ℕ in atTop, ∀ j, 0 ≤ w n j :=
    (hT.eventually (harmonic_pair_bounds rh)).mono fun _ h => h.2.1
  have hW : ∀ᶠ n : ℕ in atTop, ∀ i ∈ S n, ∀ j ∈ S n, 0 ≤ W n i * W n j :=
    hw.mono fun n hw i _ j _ =>
      mul_nonneg (monomialWeight_nonneg (w n) hw i) (monomialWeight_nonneg (w n) hw j)
  have hπ := Real.sqrt_pos.2 Real.pi_pos
  have hder : HasDerivAt (fun x : ℝ => c * x ^ 2) (1 / Real.sqrt Real.pi) 1 := by
    convert (hasDerivAt_pow 2 (1 : ℝ)).const_mul c using 1
    dsimp [c]
    norm_num
    field_simp
  have hlimit := collision_ramp_tendsto_hard S X W hW B η hB (fun x => c * x^2) 1
    (1 / Real.sqrt Real.pi) (1/2) (by norm_num) hder
  have hlocal : ∀ x : ℝ, |x - 1| < 1/2 →
      Tendsto (fun n : ℕ => B n * rampCollisionMass (S n) (X n) (W n) (x * η n))
        atTop (𝓝 (c * x^2)) := by
    intro x hx
    have hxpos : 0 < x := by linarith [(abs_lt.mp hx).1]
    let ε (n : ℕ) := x * η n
    have hε : ∀ᶠ n : ℕ in atTop, 0 < ε n := hη.mono fun _ he => mul_pos hxpos he
    have hεr : Tendsto (fun n : ℕ => ε n / s n) atTop (𝓝 0) := by
      simpa only [ε, s, mul_div_assoc, mul_zero] using hr.const_mul x
    have hεresolution : ∃ a > (0 : ℝ), ∀ᶠ n in atTop, a ≤ ε n * Real.log (T n) := by
      obtain ⟨a, ha, hbound⟩ := hresolution
      refine ⟨x*a, mul_pos hxpos ha, hbound.mono ?_⟩
      intro n hn
      simpa only [ε, mul_assoc] using mul_le_mul_of_nonneg_left hn hxpos.le
    have hF := (critical_harmonic_full_fejer_limit rh hcorr T ε hT hε hh hεr hεresolution).const_mul (x^2)
    rw [mul_comm (x^2) c] at hF
    apply hF.congr'
    filter_upwards [hε, hη] with n he hn
    change _ = B n * rampCollisionMass (piAntidiag univ n)
      (monomialFrequency (g n)) (monomialWeight (w n)) (ε n)
    rw [ramp_eq_fejer (g n) (w n) n he]
    dsimp [B, ε]
    field_simp
    ring
  have hout := hlimit hlocal
  apply hout.congr'
  filter_upwards [hη] with n hn
  simp only [one_mul]
  change (B n * η n) * _ = (s n / η n) * _
  rw [show B n * η n = s n / η n by dsimp [B]; field_simp]
  rfl

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
