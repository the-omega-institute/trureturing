/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicCollisionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The harmonic zeta collision mass approaches the Gaussian hard-band coefficient. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer
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

private theorem annulusIntegral_le (f : ℝ → ℝ) (hf : Continuous f)
    {a b D : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ t, a ≤ |t| → |t| ≤ b → f t ≤ D) :
    (∫ t in -b..b, f t) - (∫ t in -a..a, f t) ≤ 2 * (b - a) * D := by
  have hleft : (∫ t in -b..-a, f t) ≤ (∫ _ in -b..-a, D) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) ?_
    intro t ht
    have he : |t| = -t := abs_of_nonpos (by linarith [ht.2])
    apply h t <;> rw [he] <;> linarith [ht.1, ht.2]
  have hright : (∫ t in a..b, f t) ≤ (∫ _ in a..b, D) := by
    refine intervalIntegral.integral_mono_on hab (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) ?_
    intro t ht
    have he : |t| = t := abs_of_nonneg (ha.trans ht.1)
    apply h t <;> rw [he]
    · exact ht.1
    · exact ht.2
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-b) (-a)) (hf.intervalIntegrable (-a) a)
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-b) a) (hf.intervalIntegrable a b)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hleft hright
  linarith

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

private theorem logarithmic_window_decay (T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop)
    (hg : Tendsto (fun n : ℕ => (Real.log (T n)) ^ 2 / (n : ℝ)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * T n * Real.log (T n) *
      Real.exp (-(2 * c * (n : ℝ) / Real.log (T n)))) atTop (𝓝 0) := by
  let a := min c 1
  have ha : 0 < a := lt_min hc zero_lt_one
  have hac : a ≤ c := min_le_left _ _
  have ha1 : a ≤ 1 := min_le_right _ _
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) ^ 2 *
      Real.exp (-c * Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp hroot
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
  · filter_upwards [hT.eventually_gt_atTop (1 : ℝ)] with n hTn
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
      (Real.log_pos hTn).le) (Real.exp_pos _).le
  · filter_upwards [hT.eventually_gt_atTop (1 : ℝ), hg.eventually_lt_const (sq_pos_of_pos ha),
      eventually_gt_atTop (0 : ℕ)] with n hTn hgn hn
    let q := Real.sqrt (n : ℝ)
    let p := Real.log (T n)
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hq : 0 < q := Real.sqrt_pos.2 hn'
    have hp : 0 < p := Real.log_pos hTn
    have hq2 : q ^ 2 = (n : ℝ) := Real.sq_sqrt hn'.le
    have hp2 : p ^ 2 ≤ (a * q) ^ 2 := by
      rw [mul_pow, hq2]
      exact ((div_lt_iff₀ hn').mp hgn).le
    have hpa : p ≤ a * q :=
      (sq_le_sq₀ hp.le (mul_nonneg ha.le hq.le)).mp hp2
    have hpq : p ≤ q := hpa.trans (by simpa using mul_le_mul_of_nonneg_right ha1 hq.le)
    have hpc : p ≤ c * q := hpa.trans (mul_le_mul_of_nonneg_right hac hq.le)
    have hquot : q ≤ (n : ℝ) / p := by
      rw [le_div_iff₀ hp, ← hq2, pow_two]
      exact mul_le_mul_of_nonneg_left hpq hq.le
    have hexp : p - 2 * c * (n : ℝ) / p ≤ -c * q := by
      rw [mul_div_assoc]
      linarith only [hpc, mul_le_mul_of_nonneg_left hquot (show 0 ≤ 2 * c by positivity)]
    have heq : q * T n * p * Real.exp (-(2 * c * (n : ℝ) / p)) =
        (q * p) * Real.exp (p - 2 * c * (n : ℝ) / p) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (show 0 < T n by linarith)]
      ring
    change q * T n * p * Real.exp (-(2 * c * (n : ℝ) / p)) ≤ q ^ 2 * Real.exp (-c * q)
    rw [heq]
    exact mul_le_mul (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hpq hq.le)
      (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (sq_nonneg _)

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHPeriodicPhaseCoverage
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase)
open D5.S3.Fourier.Concentration.FejerCollisionLimit

def harmonicOrdinate (rh : RiemannHypothesis) (T : ℝ) :
    ↥(positiveCutoff rh T) → ℝ := fun j => ordinate j.1

def harmonicProbability (rh : RiemannHypothesis) (T : ℝ) :
    ↥(positiveCutoff rh T) → ℝ := fun j => harmonicWeight j.1 / harmonicMass rh T

def harmonicScale (rh : RiemannHypothesis) (T : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * pairMoment (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) 2 / 2)

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

private theorem score_power_le_exp (x q : ℝ) (hx : 0 ≤ x) (h : q ≤ 1 - x) (n : ℕ) :
    x ^ (2 * n) ≤ Real.exp (-(2 * q * n)) := by
  have hx' : x ≤ Real.exp (-q) := (by linarith : x ≤ -q + 1).trans (Real.add_one_le_exp _)
  calc
    x ^ (2 * n) ≤ Real.exp (-q) ^ (2 * n) := pow_le_pow_left₀ hx hx' _
    _ = Real.exp (-(2 * q * n)) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf

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
