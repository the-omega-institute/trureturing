/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHCriticalPairSumThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive upper threshold for the pair sum yields the critical harmonic zeta collision limit. -/

import D5.S3.Fourier.Concentration.ExponentialTentEnergy
import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.OmittedSpectrumCutoff
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
import D5.S3.Weil.ZetaExplicit.LandauUniformCutoff

/-! The Lorentzian pair sum controls the height of each finite phase peak.
A strict threshold for the pair sum extends the collision limit to resolutions
with an eventual positive lower bound on the product of resolution and log-height. -/

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalPairSumThreshold

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
  (band_deficit)
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

private lemma phase_change (g t u : ℝ) :
    ‖phase g t - phase g (t - u)‖ ≤ |g| * |u| := by
  simpa only [phase, sub_sub_cancel, mul_comm, mul_left_comm, mul_assoc] using
    (unit_phase_diff g t (t - u))

private theorem score_cube_le_energy {J : Type*} [Fintype J]
    (g w : J → ℝ) (Y t : ℝ) (hY : 1 ≤ Y)
    (hg : ∀ j, |g j| ≤ Y) (hw : ∀ j, 0 ≤ w j)
    (hi : Integrable (fun u : ℝ =>
      Real.exp (-2 * |u|) * ‖complexScore g w (t-u)‖ ^ 2)) :
    ‖complexScore g w t‖ ^ 3 ≤ (3 / 2 * Real.exp (2 / Y) * Y * (∑ j, w j)) *
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
    change ‖complexScore g w t‖ ^ 3 ≤ (3 / 2 * Real.exp (2 / Y) * Y * M) * _
    simp [← hM, hz]
  · let f (u : ℝ) := ‖complexScore g w (t - u)‖
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
    have hL : 0 < Y * M := mul_pos (by linarith) hM
    have hpeak := D5.S3.Fourier.Concentration.ExponentialTentEnergy.cube_le_exponential_energy f hL
      (fun _ => norm_nonneg _) (fun u => by linarith [hshift u]) hi
    have hratio : f 0 / (Y * M) ≤ 1 / Y := by
      apply (div_le_iff₀ hL).2
      rw [← mul_assoc, one_div_mul_cancel (by linarith : Y ≠ 0), one_mul]
      simpa only [f, sub_zero] using hbound t
    have hcoef : 3 / 2 * Real.exp (2 * (f 0 / (Y * M))) * (Y * M) ≤
        3 / 2 * Real.exp (2 / Y) * Y * M := by
      rw [mul_assoc (3 / 2 * _)]
      gcongr
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
    have henergy : 0 ≤ ∫ u : ℝ, Real.exp (-2 * |u|) * f u ^ 2 :=
      integral_nonneg (fun u => mul_nonneg (Real.exp_nonneg _) (sq_nonneg (f u)))
    simpa only [f, sub_zero, M] using
      hpeak.trans (mul_le_mul_of_nonneg_right hcoef henergy)

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
      (3 / 2 * Real.exp (2 / Y) * Y * S.N Y) *
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
  change _ ≤ (3 / 2 * Real.exp (2 / Y) * Y * ∑ j, w j) * (∫ u : ℝ, exponentialWeight u * ‖complexScore g w (t-u)‖ ^ 2) at hc
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

/-- A vanishing normalized pair bound gives a vanishing normalized phase peak. -/
theorem cutoff_small_of_pair_bound (S : Spectrum) (hN : CountAsymptotic S)
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
  let A₀ := 3 / 2 * Real.exp 2 * C / (2 * Real.pi)
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
    _ ≤ (3 / 2 * Real.exp (2 / Y) * Y * S.N Y) * (Y * Real.log Y / (2 * Real.pi) * F) := hg
    _ ≤ (3 / 2 * Real.exp (2 / Y) * Y * S.N Y) * (Y * Real.log Y / (2 * Real.pi) * (δ * Real.log Y)) := by
      gcongr
      exact hcorrY t htl htu
    _ ≤ (3 / 2 * Real.exp 2 * Y * (C * (Y * Real.log Y))) *
        (Y * Real.log Y / (2 * Real.pi) * (δ * Real.log Y)) := by
      have hExp : Real.exp (2 / Y) ≤ Real.exp 2 :=
        Real.exp_le_exp.mpr ((div_le_iff₀ hYpos).2 (by linarith))
      gcongr
    _ = (A₀ * δ) * (Y * Real.log Y)^3 := by dsimp [A₀]; ring
    _ = _ := by rw [hδeq]; ring

/-- A positive upper threshold for the unnormalized pair sum on fixed logarithmic bands. -/
def MontgomeryThresholdOnLogBands (S : Spectrum) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ < 2 * (1 / (2 * Real.pi)) ^ 2 / 3 ∧
    ∀ A > (1 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y ≤
          κ * Y * (Real.log Y) ^ 2

private theorem cutoff_fractional_deficit (S : Spectrum) (hN : CountAsymptotic S)
    (hpair : MontgomeryThresholdOnLogBands S) :
    ∃ d > (0 : ℝ), ∀ A > (1 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        d * (S.N Y : ℝ) ≤ (S.N Y : ℝ) -
          ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖ := by
  obtain ⟨κ, hκ, hκmax, hpair⟩ := hpair
  let c : ℝ := 1 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hκc : (3 / 2 : ℝ) * κ < c ^ 2 := by
    change κ < 2 * c ^ 2 / 3 at hκmax
    linarith
  let θ : ℝ := ((3 / 2) * κ / c ^ 2 + 1) / 2
  have hθ : θ < 1 := by
    dsimp [θ]
    linarith [(div_lt_one (sq_pos_of_pos hc)).2 hκc]
  have hstrict : 3 / 2 * κ < θ * c ^ 2 := by
    dsimp [θ]
    field_simp
    nlinarith [mul_pos (sq_pos_of_pos hc) (sub_pos.mpr hκc)]
  have he : Tendsto (fun Y : ℝ => 2 / Y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.const_mul (2 : ℝ))
  have hexp : Tendsto (fun Y : ℝ => Real.exp (2 / Y)) atTop (𝓝 1) := by
    have h : Tendsto Real.exp (𝓝 0) (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.continuousAt
    rw [Real.exp_zero] at h
    exact h.comp he
  have hcoef : Tendsto (fun Y : ℝ => 3 / 2 * Real.exp (2 / Y) * κ) atTop
      (𝓝 (3 / 2 * κ)) := by
    simpa only [mul_one] using (hexp.const_mul (3 / 2 : ℝ)).mul_const κ
  have hcount : Tendsto (fun Y : ℝ => θ * ((S.N Y : ℝ) / (Y * Real.log Y)) ^ 2) atTop
      (𝓝 (θ * c ^ 2)) := (hN.pow 2).const_mul θ
  refine ⟨(1 - θ) / 3, by linarith, ?_⟩
  intro A hA
  filter_upwards [hcoef.eventually_lt hcount hstrict, hpair A hA, eventually_gt_atTop (1 : ℝ)]
    with Y hsmall hGY hY
  intro t htl htu
  let b := ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖
  let N : ℝ := S.N Y
  have hYp : 0 < Y := by linarith
  have hYlog : 0 < Y * Real.log Y := mul_pos hYp (Real.log_pos hY)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hb : b ≤ N := by
    unfold b N Spectrum.N
    rw [Nat.cast_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      simp [norm_phase])
  have hcub : b ^ 3 ≤ (3 / 2 * Real.exp (2 / Y) * κ) * (Y * Real.log Y) ^ 2 * N := by
    refine (cutoff_cube_le_montgomery S hY t).trans ?_
    calc
      _ ≤ (3 / 2 * Real.exp (2 / Y) * Y * N) * (κ * Y * (Real.log Y) ^ 2) :=
        mul_le_mul_of_nonneg_left (hGY t htl htu) (by positivity)
      _ = _ := by ring
  have hsmall' : (3 / 2 * Real.exp (2 / Y) * κ) * (Y * Real.log Y) ^ 2 ≤ θ * N ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (le_of_lt hsmall) (sq_nonneg (Y * Real.log Y))
    simp only [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hYlog.ne')] at h ⊢
    exact h
  have hbc : b ^ 3 ≤ θ * N ^ 3 := by
    calc
      _ ≤ _ := hcub
      _ ≤ (θ * N ^ 2) * N := mul_le_mul_of_nonneg_right hsmall' hN0
      _ = _ := by ring
  change ((1 - θ) / 3) * N ≤ N - b
  rcases hN0.eq_or_lt with hNzero | hNpos
  · have hbzero : b = 0 := le_antisymm (hNzero ▸ hb) (norm_nonneg _)
    rw [← hNzero, hbzero]
    simp
  have hf : 0 ≤ (N - b) ^ 2 * (2 * N + b) :=
    mul_nonneg (sq_nonneg _) (add_nonneg (by positivity) (norm_nonneg _))
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hNpos)).mp
  nlinarith only [hbc, hf]

private theorem harmonic_long_deficit_of_threshold (rh : RiemannHypothesis)
    (hpair : MontgomeryThresholdOnLogBands (zetaSpectrum rh)) :
    ∀ A > (1 : ℝ), ∃ d > (0 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        d / Real.log Y ≤
          1 - ‖complexScore (harmonicOrdinate rh Y) (harmonicProbability rh Y) t‖ := by
  classical
  let S := zetaSpectrum rh
  let c : ℝ := 1 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hN : CountAsymptotic S := zetaSpectrum_countAsymptotic rh
  obtain ⟨d, hd, hdeficit⟩ := cutoff_fractional_deficit S hN hpair
  have hmass : Tendsto (fun Y : ℝ => harmonicMass rh Y / (Real.log Y)^2) atTop (𝓝 (c/2)) := by
    convert harmonic_mass_limit rh using 2 <;> dsimp [c] <;> ring
  intro A hA
  refine ⟨d / 4, by positivity, ?_⟩
  filter_upwards [hdeficit A hA, hN.eventually_const_lt (show c / 2 < c by linarith),
    hmass.eventually_lt_const (show c / 2 < c by linarith), eventually_gt_atTop (1 : ℝ)]
    with Y hdef hn hm hY
  intro t htl htu
  let s := positiveCutoff rh Y
  let m (j : PositiveZetaZero) : ℝ := Zeta23.zeroMult j.val
  let W := harmonicMass rh Y
  let Z := ∑ j ∈ s, (harmonicWeight j : ℂ) * phase (ordinate j) t
  have hYpos : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hdom (j : PositiveZetaZero) (hj : j ∈ s) :
      (1 / (2 * Y)) * m j ≤ harmonicWeight j := by
    have hupper := (cutoff_mem rh Y j).mp hj
    have hlower : 6 < ordinate j := six_lt_height rh j.property.2 j.property.1.1
    have hratio : 1 / (2 * Y) ≤ ordinate j / (1 / 4 + (ordinate j) ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_nonneg (sub_nonneg.mpr hupper) (show 0 ≤ ordinate j by linarith),
        mul_nonneg (sub_nonneg.mpr (show (1 / 2 : ℝ) ≤ ordinate j by linarith))
          (show 0 ≤ ordinate j + 1 / 2 by linarith)]
    rw [mul_comm, harmonicWeight, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
  have hD := band_deficit s s (fun j => phase (ordinate j) t) harmonicWeight m
    (c := 1 / (2 * Y)) (by positivity) (Finset.Subset.refl _) (fun j _ => weight_nonneg j)
    hdom (fun j _ => norm_phase _ _)
  have hsum : ∑ j ∈ s, m j = (S.N Y : ℝ) := by
    rw [Spectrum.N, Nat.cast_sum]
    rfl
  rw [hsum] at hD
  change _ ≤ W - ‖Z‖ at hD
  have hcount : c / 2 * (Y * Real.log Y) ≤ (S.N Y : ℝ) :=
    (lt_div_iff₀ (mul_pos hYpos hlog)).mp hn |>.le
  have hraw : (d * c / 4) * Real.log Y ≤ W - ‖Z‖ := by
    calc
      _ = (1 / (2 * Y)) * (d * (c / 2 * (Y * Real.log Y))) := by field_simp; ring
      _ ≤ (1 / (2 * Y)) * (d * (S.N Y : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount hd.le) (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hdef t htl htu) (by positivity)).trans hD
  have hWpos : 0 < W := by
    have h : 0 < d * c / 4 * Real.log Y := by positivity
    linarith [norm_nonneg Z]
  have hWup : W ≤ c * (Real.log Y)^2 :=
    (div_lt_iff₀ (sq_pos_of_pos hlog)).mp hm |>.le
  let Q := complexScore (harmonicOrdinate rh Y) (harmonicProbability rh Y) t
  have hZ : Q = Z / (W : ℂ) := by
    unfold Q complexScore
    change (∑ j : ↥s, ((harmonicWeight j.1 / W : ℝ) : ℂ) * phase (ordinate j.1) t) = _
    rw [Finset.sum_coe_sort s (fun j => ((harmonicWeight j / W : ℝ) : ℂ) *
      phase (ordinate j) t)]
    dsimp [Z]
    simp_rw [Complex.ofReal_div, div_mul_eq_mul_div]
    rw [Finset.sum_div]
  have hnorm : ‖Z‖ = W * ‖Q‖ := by
    rw [hZ, Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWpos]
    field_simp
  have hscaled : (d * c / 4) * Real.log Y ≤ W * (1 - ‖Q‖) := by
    rw [hnorm] at hraw
    linarith
  have hD₀ : 0 ≤ 1 - ‖Q‖ :=
    nonneg_of_mul_nonneg_right ((by positivity : 0 ≤ (d * c / 4) * Real.log Y).trans hscaled) hWpos
  have hh := hscaled.trans (mul_le_mul_of_nonneg_right hWup hD₀)
  change d / 4 / Real.log Y ≤ 1 - ‖Q‖
  apply (div_le_iff₀ hlog).mpr
  apply (mul_le_mul_iff_right₀ (mul_pos hc hlog)).mp
  nlinarith only [hh]


private theorem critical_window_deficit (rh : RiemannHypothesis) (A : ℝ) {d : ℝ}
    (hlong : ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, Real.log H ≤ |t| → |t| ≤ A * Real.log H →
      d / Real.log H ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖) :
    ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, 1 / H ≤ |t| → |t| ≤ A * Real.log H →
      min (1 / 1048576) d / Real.log H ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖ := by
  obtain ⟨C,hC,henv⟩ := actual_cutoff_landau_envelope rh
  have h₁ := whole_log_window_deficit rh C hC (fun V t hV ht => by
    refine (henv V t hV ht).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have hnonneg : 0 ≤ Real.exp (|t| / 2) * (1 + Real.log V) := by
      have := Real.log_nonneg hV.le
      positivity
    linarith)
  filter_upwards [h₁, hlong, eventually_gt_atTop (1 : ℝ)] with H hshort hband hH
  intro t hlo hhi
  have hlog := (Real.log_pos hH).le
  by_cases hb : |t| ≤ Real.log H
  · have hh := hshort t hlo hb
    rw [← div_div] at hh
    exact (div_le_div_of_nonneg_right (min_le_left _ _) hlog).trans hh
  · exact (div_le_div_of_nonneg_right (min_le_right _ _) hlog).trans (hband t (le_of_not_ge hb) hhi)


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
    (hband : ∀ A > (1 : ℝ), ∃ d > (0 : ℝ), ∀ᶠ H : ℝ in atTop,
      ∀ t : ℝ, Real.log H ≤ |t| → |t| ≤ A * Real.log H →
        d / Real.log H ≤
          1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖)
    (T η : ℕ → ℝ)
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
  obtain ⟨d, hd, hdeficit⟩ := hband A hA
  have hmin : 0 < min (1 / 1048576 : ℝ) d := lt_min (by positivity) hd
  have hz := harmonic_multiple_log_annulus_limit_of_deficit rh T η A hA.le hmin hT hη hh
    (critical_window_deficit rh A hdeficit)
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
    (hband : ∀ A > (1 : ℝ), ∃ d > (0 : ℝ), ∀ᶠ H : ℝ in atTop,
      ∀ t : ℝ, Real.log H ≤ |t| → |t| ≤ A * Real.log H →
        d / Real.log H ≤
          1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖)
    (T η : ℕ → ℝ)
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
  exact critical_harmonic_full_fejer_limit rh hband T ε hT hε hh hεr hεresolution

/-- The critical collision limit from a positive harmonic deficit on each long band. -/
theorem harmonic_zeta_critical_collision_limit_of_long_deficit (rh : RiemannHypothesis)
    (hband : ∀ A > (1 : ℝ), ∃ d > (0 : ℝ), ∀ᶠ H : ℝ in atTop,
      ∀ t : ℝ, Real.log H ≤ |t| → |t| ≤ A * Real.log H →
        d / Real.log H ≤
          1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖)
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
  apply (normalized_critical_harmonic_collision_limit rh hband T η hT hη hh hr hresolution).congr'
  filter_upwards with n
  unfold harmonicProbability
  rw [normalized_collision_eq_div_mass]
  rw [div_mul_div_comm]
  rfl

/-- A positive upper pair-sum threshold still gives the critical Gaussian collision limit. -/
theorem harmonic_zeta_critical_collision_limit_of_threshold (rh : RiemannHypothesis)
    (hcorr : MontgomeryThresholdOnLogBands (zetaSpectrum rh))
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
  harmonic_zeta_critical_collision_limit_of_long_deficit rh
    (harmonic_long_deficit_of_threshold rh hcorr) T η hT hη hh hresolution

#print axioms harmonic_zeta_critical_collision_limit_of_threshold

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHCriticalPairSumThreshold
