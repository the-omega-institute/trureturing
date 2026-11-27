/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The harmonic zeta collision mass approaches the Gaussian hard-band coefficient. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicAnnulusDecay
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHPeriodicPhaseCoverage
import D5.S3.Fourier.Concentration.FejerCollisionLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import D5.S3.Fourier.Concentration.FejerRelativeLocalization
import D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal

open Finset Filter Set MeasureTheory
open scoped Topology
open D5.S3.Fourier.Concentration.FejerRelativeLocalization
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
open D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
open D5.S3.Analytic.Fourier.AngularFejerKernel

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHPeriodicPhaseCoverage
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase)
open D5.S3.Fourier.Concentration.FejerCollisionLimit


private theorem centralIntegral_scale {J : Type*} [Fintype J]
    (g w : J → ℝ) (n : ℕ) {s η A : ℝ} (hs : 0 < s) (hη : 0 < η) :
    s / η * (∫ t in -(A / s)..A / s, K η t * ‖complexScore g w t‖^(2*n)) =
      1 / (2 * Real.pi) * (∫ u in -A..A,
        Real.sinc ((η / s) * u / 2)^2 * ‖complexScore g w (u / s)‖^(2*n)) := by
  let F (u : ℝ) := Real.sinc ((η / s) * u / 2)^2 * ‖complexScore g w (u / s)‖^(2*n)
  have h (t : ℝ) : K η t * ‖complexScore g w t‖^(2*n) = η/(2*Real.pi)*F (s*t) := by
    have he : s*t/s=t := by field_simp
    have he' : (η/s)*(s*t)/2=η*t/2 := by field_simp
    simp only [K,F,he,he']
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hs.ne']
  simp only [smul_eq_mul]
  rw [show s * -(A/s) = -A by field_simp, show s*(A/s)=A by field_simp]
  field_simp
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp [F]
  congr 3
  ring

private theorem relativeLimit {F I e : ℕ → ℝ} {c : ℝ}
    (hi : Tendsto I atTop (𝓝 c)) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, I n ≤ F n ∧ F n - I n ≤ e n * F n) :
    Tendsto F atTop (𝓝 c) := by
  have hd : Tendsto (fun n => 1 - e n) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hu : Tendsto (fun n => I n / (1 - e n)) atTop (𝓝 c) := by
    simpa only [Pi.div_def, div_one] using hi.div hd one_ne_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hi hu (hb.mono fun _ h => h.1)
  filter_upwards [hb, hd.eventually (eventually_gt_nhds (show (0:ℝ) < 1 by norm_num))] with n hn hp
  exact (le_div_iff₀ hp).2 (by linarith [hn.2])

theorem whole_log_window_deficit (rh : RiemannHypothesis) (C : ℝ) (hC : 0 < C)
    (hLandau : ∀ V t : ℝ, 1 < V → 0 < |t| →
      ‖∑ j ∈ positiveCutoff rh V, (Zeta23.zeroMult j.val : ℂ) * phase (ordinate j) t‖ ≤
        C * (V + Real.exp (|t| / 2) * (1 + |t|)^2 +
          Real.exp (|t| / 2) * (1 + Real.log V) + Real.log V / |t|)) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, 1 / T ≤ |t| → |t| ≤ Real.log T →
      1 / (1048576 * Real.log T) ≤
        1 - ‖complexScore (harmonicOrdinate rh T) (harmonicProbability rh T) t‖ := by
  obtain ⟨L₁, hL₁, hshort⟩ := harmonic_reciprocal_time_deficit rh
  obtain ⟨L₂, b, _, hb, hperiod⟩ := harmonic_periodic_phase_deficit rh
  obtain ⟨L₃, _, hlong⟩ := harmonic_landau_window_deficit rh b C hb hC hLandau
  have hc : 0 < 16 * Real.pi := by positivity
  filter_upwards [eventually_ge_atTop L₁, eventually_ge_atTop L₂, eventually_ge_atTop L₃,
    eventually_ge_atTop (16 * Real.pi * L₁),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (16 * Real.pi)] with T hT₁ hT₂ hT₃ hTL hTs
  intro t hlo hhi
  have hT : 1 < T := hL₁.trans_le hT₁
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hp : 0 < Real.log T := Real.log_pos hT
  have ht : 0 < |t| := (one_div_pos.mpr hTpos).trans_le hlo
  by_cases hsmall : |t| ≤ 16 * Real.pi / T
  · have htL : |t| ≤ 1 / L₁ := hsmall.trans ((div_le_div_iff₀ hTpos (by linarith)).2
      (by simpa using hTL))
    have htS : |t| ≤ 1 / Real.sqrt T := hsmall.trans
      ((div_le_div_iff₀ hTpos (Real.sqrt_pos.2 hTpos)).2 (by
        simpa only [one_mul, Real.mul_self_sqrt hTpos.le] using
          mul_le_mul_of_nonneg_right hTs (Real.sqrt_nonneg T)))
    have hinv : Real.sqrt T ≤ |t|⁻¹ :=
      (le_inv_comm₀ (Real.sqrt_pos.2 hTpos) ht).2 (by simpa [one_div] using htS)
    have hlog := Real.log_le_log (Real.sqrt_pos.2 hTpos) hinv
    rw [Real.log_sqrt hTpos.le] at hlog
    apply le_trans ?_ (hshort T t hT₁ hlo htL)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right hlog hp.le]
  · by_cases hmid : |t| ≤ b / Real.log T
    · exact (div_le_div_of_nonneg_left zero_le_one (by positivity)
        (mul_le_mul_of_nonneg_right (by norm_num) hp.le)).trans
        (hperiod T t hT₂ (le_of_not_ge hsmall) hmid)
    · exact (div_le_div_of_nonneg_left zero_le_one (by positivity)
        (mul_le_mul_of_nonneg_right (by norm_num) hp.le)).trans
        (hlong T t hT₃ (le_of_not_ge hmid) hhi)

theorem harmonic_central_window_limit (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hr : Tendsto (fun n : ℕ => η n / harmonicScale rh T n) atTop (𝓝 0)) :
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

theorem harmonic_multiple_log_annulus_limit (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (B : ℝ) (hB : 1 ≤ B)
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
  exact harmonic_multiple_log_annulus_limit_of_deficit rh T η B hB
    (show (0 : ℝ) < 1 / 1048576 by positivity) hT hη hh
    (by simpa only [div_div] using hd)

/-- Compare the normalized full and truncated Fejér integrals using a relative tail. -/
theorem harmonic_fejer_relative_control (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    {n : ℕ} {R : ℝ} (he : 0 < η n) (hR : 1 ≤ η n * R)
    (hw : ∀ j, 0 ≤ harmonicProbability rh (T n) j) :
    let F (t : ℝ) := K (η n) t *
      ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n)
    let whole := harmonicScale rh T n / η n * ∫ t : ℝ, F t
    let inner := harmonicScale rh T n / η n * ∫ t in -R..R, F t
    inner ≤ whole ∧ whole - inner ≤ (64 / (η n * R)) * whole := by
  intro F whole inner
  have hRpos : 0 < R := pos_of_mul_pos_right (zero_lt_one.trans_le hR) he.le
  have hwhole : Integrable F := by
    dsimp [F]
    simp_rw [moment_eq_pair]
    exact kernel_pair_integrable _ _ _ he
  have hnn (t : ℝ) : 0 ≤ F t := mul_nonneg ((fejer_law he).1 t) (by positivity)
  have hle : (∫ t in -R..R, F t) ≤ ∫ t : ℝ, F t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hwhole (ae_of_all _ hnn)
  have hrel := relative_fejer_truncation (harmonicOrdinate rh (T n))
    (harmonicProbability rh (T n)) hw n he hR
  have hs : 0 ≤ harmonicScale rh T n / η n := by unfold harmonicScale; positivity
  refine ⟨mul_le_mul_of_nonneg_left hle hs, ?_⟩
  dsimp only [whole, inner]
  rw [← mul_sub]
  convert mul_le_mul_of_nonneg_left hrel hs using 1
  ring

private theorem harmonic_full_fejer_limit (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hr : Tendsto (fun n : ℕ => η n / harmonicScale rh T n) atTop (𝓝 0))
    (htrunc : Tendsto (fun n : ℕ => η n * Real.log (T n)) atTop atTop)
    (hd : ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, 1 / H ≤ |t| → |t| ≤ Real.log H →
      1 / (1048576 * Real.log H) ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖) :
    Tendsto (fun n : ℕ => harmonicScale rh T n / η n *
      ∫ t : ℝ, K (η n) t *
        ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n))
      atTop (𝓝 (1 / (2 * Real.sqrt Real.pi))) := by
  let F (n : ℕ) (t : ℝ) := K (η n) t *
    ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n)
  let s := harmonicScale rh T
  have hd' : ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, 1 / H ≤ |t| → |t| ≤ 1 * Real.log H →
      1 / (1048576 * Real.log H) ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖ := by
    simpa only [one_mul] using hd
  have hann := harmonic_multiple_log_annulus_limit rh T η 1 le_rfl hT hη hh hd'
  have hcenter := harmonic_central_window_limit rh T η hT hη hh hr
  have hinner : Tendsto (fun n : ℕ => s n / η n *
      ∫ t in -Real.log (T n)..Real.log (T n), F n t) atTop
        (𝓝 (1 / (2 * Real.sqrt Real.pi))) := by
    simpa only [add_zero] using (hcenter.add hann).congr
      (fun n : ℕ => by dsimp [F, s]; simp only [one_mul]; ring)
  apply relativeLimit hinner (htrunc.const_div_atTop 64)
  filter_upwards [hη, htrunc.eventually_ge_atTop 1, hT.eventually (harmonic_pair_bounds rh)]
    with n he hR hw
  exact harmonic_fejer_relative_control rh T η he hR hw.2.1

open D5.S3.Fourier.Concentration.FejerCollisionSecants (rampCollisionMass)

private theorem ramp_eq_fejer {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    rampCollisionMass (piAntidiag univ n) (monomialFrequency g) (monomialWeight w) η =
      η * (∫ t : ℝ, K η t * ‖complexScore g w t‖^(2*n)) := by
  rw [(fejer_collision_comparison g w n hη).1]
  unfold rampCollisionMass
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show η * (monomialWeight w i * monomialWeight w j *
      phi η (monomialFrequency g i - monomialFrequency g j)) =
      monomialWeight w i * monomialWeight w j *
        (η * phi η (monomialFrequency g i - monomialFrequency g j)) by ring]
  congr 1
  unfold phi
  rw [mul_max_of_nonneg _ _ hη.le, mul_zero]
  congr 1
  field_simp

theorem normalized_harmonic_collision_limit_of_fejer (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hfejer : ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => harmonicScale rh T n / (x * η n) *
        ∫ t : ℝ, K (x * η n) t *
          ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n))
        atTop (𝓝 (1 / (2 * Real.sqrt Real.pi)))) :
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
    have hF := (hfejer x hxpos).const_mul (x^2)
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

theorem normalized_collision_eq_div_mass {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (M : ℝ) (n : ℕ) (r : ℝ) :
    tailCollisionMass g (fun j => w j / M) n r =
      tailCollisionMass g w n r / M^(2*n) := by
  have hweight (k : J → ℕ) (hk : k ∈ piAntidiag univ n) :
      monomialWeight (fun j => w j / M) k = monomialWeight w k / M^n := by
    simp only [monomialWeight, div_pow, Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum, (Finset.mem_piAntidiag.mp hk).1, ← mul_div_assoc]
  unfold tailCollisionMass nearCollisionMass
  simp_rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  by_cases h : |monomialFrequency g i - monomialFrequency g j| ≤ r
  · rw [ite_eq_left h, ite_eq_left h, hweight i hi, hweight j hj, div_mul_div_comm]
    rw [show 2*n = n+n by omega, pow_add]
  · simp [h]

/-- The original harmonic collision mass has a Gaussian limit under the uniform Landau envelope. -/
theorem harmonic_zeta_collision_limit (rh : RiemannHypothesis) (C : ℝ) (hC : 0 < C)
    (hLandau : ∀ V t : ℝ, 1 < V → 0 < |t| →
      ‖∑ j ∈ positiveCutoff rh V, (Zeta23.zeroMult j.val : ℂ) * phase (ordinate j) t‖ ≤
        C * (V + Real.exp (|t| / 2) * (1 + |t|)^2 +
          Real.exp (|t| / 2) * (1 + Real.log V) + Real.log V / |t|))
    (T η : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (htrunc : Tendsto (fun n : ℕ => η n * Real.log (T n)) atTop atTop) :
    let scale (n : ℕ) := Real.sqrt ((n : ℝ) * pairMoment
      (fun j : ↥(positiveCutoff rh (T n)) => ordinate j.1)
      (fun j => harmonicWeight j.1 / harmonicMass rh (T n)) 2 / 2)
    Tendsto (fun n : ℕ => η n / scale n) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => scale n *
      tailCollisionMass (fun j : ↥(positiveCutoff rh (T n)) => ordinate j.1)
        (fun j => harmonicWeight j.1) n (η n) /
        (η n * harmonicMass rh (T n)^(2*n))) atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  intro scale hr
  have hd := whole_log_window_deficit rh C hC hLandau
  change Tendsto (fun n => η n / harmonicScale rh T n) atTop (𝓝 0) at hr
  apply (normalized_harmonic_collision_limit_of_fejer rh T η hT hη (fun x hx => by
    let ε (n : ℕ) := x * η n
    have hε : ∀ᶠ n : ℕ in atTop, 0 < ε n := hη.mono fun _ he => mul_pos hx he
    have hεr : Tendsto (fun n : ℕ => ε n / harmonicScale rh T n) atTop (𝓝 0) := by
      simpa only [ε, mul_div_assoc, mul_zero] using hr.const_mul x
    have hεtrunc : Tendsto (fun n : ℕ => ε n * Real.log (T n)) atTop atTop := by
      simpa only [ε, mul_assoc] using htrunc.const_mul_atTop hx
    exact harmonic_full_fejer_limit rh T ε hT hε hh hεr hεtrunc hd)).congr'
  filter_upwards with n
  unfold harmonicProbability
  rw [normalized_collision_eq_div_mass]
  rw [div_mul_div_comm]
  rfl

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
