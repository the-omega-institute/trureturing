/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicAnnulusDecay
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLogarithmicAnnulusDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive logarithmic phase deficit suppresses the actual harmonic zeta annulus. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHPeriodicPhaseCoverage
import D5.S3.Fourier.Concentration.FejerCollisionLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import D5.S3.Fourier.Concentration.FejerRelativeLocalization
import D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal

/-! Annulus decay for the harmonic zeta score at a fixed positive deficit coefficient. -/

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

private theorem score_power_le_exp (x q : ℝ) (hx : 0 ≤ x) (h : q ≤ 1 - x) (n : ℕ) :
    x ^ (2 * n) ≤ Real.exp (-(2 * q * n)) := by
  have hx' : x ≤ Real.exp (-q) := (by linarith : x ≤ -q + 1).trans (Real.add_one_le_exp _)
  calc
    x ^ (2 * n) ≤ Real.exp (-q) ^ (2 * n) := pow_le_pow_left₀ hx hx' _
    _ = Real.exp (-(2 * q * n)) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf

/-- A fixed positive normalized phase deficit suppresses the entire logarithmic annulus. -/
theorem harmonic_multiple_log_annulus_limit_of_deficit (rh : RiemannHypothesis) (T η : ℕ → ℝ)
    (B : ℝ) (hB : 1 ≤ B) {c : ℝ} (hc : 0 < c)
    (hT : Tendsto T atTop atTop)
    (hη : ∀ᶠ n : ℕ in atTop, 0 < η n)
    (hh : Tendsto (fun n : ℕ => (Real.log (T n))^2 / (n : ℝ)) atTop (𝓝 0))
    (hd : ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, 1 / H ≤ |t| → |t| ≤ B * Real.log H →
      c / Real.log H ≤
        1 - ‖complexScore (harmonicOrdinate rh H) (harmonicProbability rh H) t‖) :
    let F (n : ℕ) (t : ℝ) := K (η n) t *
      ‖complexScore (harmonicOrdinate rh (T n)) (harmonicProbability rh (T n)) t‖^(2*n)
    Tendsto (fun n : ℕ => harmonicScale rh T n / η n *
      ((∫ t in -(B * Real.log (T n))..B * Real.log (T n), F n t) -
      (∫ t in -(1 / T n)..1 / T n, F n t))) atTop (𝓝 0) := by
  intro F
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
        convert h using 2 <;> ring)
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

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLogarithmicCollisionLimit
