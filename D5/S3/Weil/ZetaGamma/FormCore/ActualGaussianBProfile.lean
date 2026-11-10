/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualGaussianBProfile
   generality: I
   mirror-B: none(waiver:actual-source-profile-identification)
   mirror-E: none(waiver:literal-Gaussian-integral-evaluation)
   anchors: []
   utility: none
   digest: Evaluate the complete theta profile and actual B image of a literal Gaussian source. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
import D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
import D5.S3.Analytic.Fourier.XiThetaTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/- The physical source and both actual operators are the repository's
original ones. The complete theta series is evaluated by HasSum; the B tail
is evaluated by a decaying primitive and a genuinely integrable derivative.
This module does not assume that B is linear, nor infer a Gamma domain from H6.
The candidate is extracted from GaussianGammaDomainCheck's exact source
calculation, with no spectral/nonzero or form-core claims included. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile

open Real Set MeasureTheory Filter
open scoped Topology
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open private fullConstant fullConstant_nonneg jet jet_decay from
  D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
open private actual_fullJet_zero_eq_phi_all from
  D5.S3.Analytic.Fourier.ThetaRadialCurvature
open private psiSecond_eq from D5.S3.Analytic.Fourier.XiThetaTransform

private def literalGaussian (a x : ℝ) : ℂ :=
  (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ)

private def cPhi : ℝ := Real.pi ^ (1 / 4 : ℝ) / 4

private def gaussianRay (a t : ℝ) : ℝ :=
  cPhi * (romikPhi (a + t / 2) + (3 / 2 : ℝ) * psi (a + t / 2) -
    3 * psiFirst (a + t / 2))

private def gaussianTailRay (a t : ℝ) : ℝ :=
  cPhi * (psi (a + t / 2) - 2 * psiFirst (a + t / 2))

private theorem phi_continuous : Continuous romikPhi := by
  rw [show romikPhi = sourceThetaKernel from funext romikPhi_eq_source]
  exact source_theta_continuous

private theorem gaussianRay_continuous (a : ℝ) : Continuous (gaussianRay a) := by
  have hp : Continuous psi := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_psi x).continuousAt)
  have hp' : Continuous psiFirst := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_psiFirst x).continuousAt)
  exact continuous_const.mul
    (((phi_continuous.comp (by fun_prop)).add
      (continuous_const.mul (hp.comp (by fun_prop)))).sub
      (continuous_const.mul (hp'.comp (by fun_prop))))

private theorem gaussianTailRay_continuous (a : ℝ) :
    Continuous (gaussianTailRay a) := by
  have hp : Continuous psi := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_psi x).continuousAt)
  have hp' : Continuous psiFirst := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_psiFirst x).continuousAt)
  exact continuous_const.mul
    ((hp.comp (by fun_prop)).sub (continuous_const.mul (hp'.comp (by fun_prop))))

private theorem gaussianRay_eq_series (a t : ℝ) :
    gaussianRay a t = Real.pi ^ (9 / 4 : ℝ) *
      exp ((9 / 2 : ℝ) * (a + t / 2)) * thetaSeries 4 (exp (2 * (a + t / 2))) := by
  let b : ℝ := a + t / 2
  have hpi : Real.pi ^ (9 / 4 : ℝ) = Real.pi ^ (1 / 4 : ℝ) * Real.pi ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast Real.pi 2, ← Real.rpow_add Real.pi_pos]
    norm_num
  have he : exp (b / 2) * exp (2 * b) ^ (2 : ℕ) = exp ((9 / 2 : ℝ) * b) := by
    rw [← Real.exp_nat_mul, ← exp_add]
    congr 1
    ring
  rw [gaussianRay, romikPhi, omega_eq_series (exp_pos _), psi_eq_series, psiFirst]
  change (Real.pi ^ (1 / 4 : ℝ) / 4) *
    (2 * exp (b / 2) *
      (2 * Real.pi ^ (2 : ℕ) * exp (2 * b) ^ (2 : ℕ) * thetaSeries 4 (exp (2 * b)) -
        3 * Real.pi * exp (2 * b) * thetaSeries 2 (exp (2 * b))) +
      (3 / 2 : ℝ) * (exp (b / 2) * thetaSeries 0 (exp (2 * b))) -
      3 * (exp (b / 2) * (thetaSeries 0 (exp (2 * b)) / 2 -
        2 * Real.pi * exp (2 * b) * thetaSeries 2 (exp (2 * b))))) = _
  calc
    _ = (Real.pi ^ (1 / 4 : ℝ) * Real.pi ^ (2 : ℕ)) *
        (exp (b / 2) * exp (2 * b) ^ (2 : ℕ)) * thetaSeries 4 (exp (2 * b)) := by ring
    _ = _ := by rw [he, ← hpi]

private theorem literalGaussian_fullHasSum (a t : ℝ) :
    HasSum (fun n : ℕ => physicalTerm (literalGaussian a) n (Real.pi * exp t))
      ((exp ((9 / 2 : ℝ) * a) * thetaSeries 4 (exp (2 * (a + t / 2))) : ℝ) : ℂ) := by
  have hs := Complex.ofRealCLM.hasSum
    ((thetaSeries_summable 4 (exp_pos (2 * (a + t / 2)))).hasSum.mul_left
      (exp ((9 / 2 : ℝ) * a)))
  have he : exp (2 * a) * exp t = exp (2 * (a + t / 2)) := by
    rw [← exp_add]
    congr 1
    ring
  have hterm (n : ℕ) :
      physicalTerm (literalGaussian a) n (Real.pi * exp t) =
        ((exp ((9 / 2 : ℝ) * a) *
          (((n : ℝ) + 1) ^ (4 : ℕ) *
            exp (-Real.pi * ((n : ℝ) + 1) ^ (2 : ℕ) *
              exp (2 * (a + t / 2)))) : ℝ) : ℂ) := by
    have hx : exp ((9 / 2 : ℝ) * a - exp (2 * a) *
          (((n : ℝ) + 1) ^ (2 : ℕ) * (Real.pi * exp t))) =
        exp ((9 / 2 : ℝ) * a) *
          exp (-Real.pi * ((n : ℝ) + 1) ^ (2 : ℕ) * exp (2 * (a + t / 2))) := by
      rw [sub_eq_add_neg, exp_add]
      congr 1
      congr 1
      calc
        -(exp (2 * a) * (((n : ℝ) + 1) ^ (2 : ℕ) * (Real.pi * exp t))) =
            -Real.pi * ((n : ℝ) + 1) ^ (2 : ℕ) * (exp (2 * a) * exp t) := by ring
        _ = _ := by rw [he]
    simp only [physicalTerm, literalGaussian, Nat.cast_add, Nat.cast_one]
    rw [hx]
    push_cast
    ring
  simpa only [thetaSeries, Complex.ofRealCLM_apply] using hs.congr_fun hterm

private theorem literalGaussian_actualProfile (a : ℝ) :
    actualGammaProfile (literalGaussian a) =
      fun t : ℝ => if 0 ≤ t then (gaussianRay a t : ℂ) else 0 := by
  funext t
  by_cases ht : 0 ≤ t
  · have hs : (Real.pi * exp t) ^ (9 / 4 : ℝ) * exp ((9 / 2 : ℝ) * a) =
        Real.pi ^ (9 / 4 : ℝ) * exp ((9 / 2 : ℝ) * (a + t / 2)) := by
      rw [Real.mul_rpow Real.pi_pos.le (exp_pos _).le, ← Real.exp_mul,
        mul_assoc, ← exp_add]
      congr 2 <;> ring
    rw [actualGammaProfile, if_pos ht, if_pos ht, fullTheta,
      (literalGaussian_fullHasSum a t).tsum_eq, gaussianRay_eq_series]
    simpa only [Complex.ofReal_mul, mul_assoc] using
      congrArg Complex.ofReal (congrArg
        (fun v : ℝ => v * thetaSeries 4 (exp (2 * (a + t / 2)))) hs)
  · simp only [actualGammaProfile, if_neg ht]

private theorem halfPhi_bound {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    |romikPhi (a + t / 2)| ≤ fullConstant 0 * exp (-t / 2) := by
  simpa only [jet, actual_fullJet_zero_eq_phi_all, Real.norm_eq_abs,
    neg_div] using jet_decay ha 0 (show 0 ≤ t / 2 by positivity)

private def gaussianRaySize : ℝ := cPhi * ((11 / 2 : ℝ) * fullConstant 0)
private def gaussianTailSize : ℝ := cPhi * (3 * fullConstant 0)

private theorem gaussianRaySize_nonneg : 0 ≤ gaussianRaySize := by
  have h := fullConstant_nonneg 0
  dsimp [gaussianRaySize, cPhi]
  positivity

private theorem gaussianTailSize_nonneg : 0 ≤ gaussianTailSize := by
  have h := fullConstant_nonneg 0
  dsimp [gaussianTailSize, cPhi]
  positivity

private theorem ray_bounds {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    |gaussianRay a t| ≤ gaussianRaySize * exp (-t / 2) ∧
      |gaussianTailRay a t| ≤ gaussianTailSize * exp (-t / 2) := by
  let b : ℝ := a + t / 2
  have h0 := halfPhi_bound ha ht
  have hp := psi_bounds (show 0 ≤ b by dsimp [b]; linarith)
  rw [← romikPhi_eq_source] at hp
  have hp0 : |psi b| ≤ fullConstant 0 * exp (-t / 2) :=
    hp.1.trans ((le_abs_self _).trans h0)
  have hp1 : |psiFirst b| ≤ fullConstant 0 * exp (-t / 2) :=
    hp.2.trans ((le_abs_self _).trans h0)
  have hsum := abs_add_le (romikPhi b) ((3 / 2 : ℝ) * psi b)
  have hsub := abs_sub_le (romikPhi b + (3 / 2 : ℝ) * psi b) 0 (3 * psiFirst b)
  have htail := abs_sub_le (psi b) 0 (2 * psiFirst b)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 3),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsum hsub htail
  constructor
  · rw [gaussianRay, abs_mul, abs_of_nonneg (by dsimp [cPhi]; positivity)]
    apply (mul_le_mul_of_nonneg_left
      (show |romikPhi b + (3 / 2 : ℝ) * psi b - 3 * psiFirst b| ≤
        (11 / 2 : ℝ) * fullConstant 0 * exp (-t / 2) by linarith)
      (by dsimp [cPhi]; positivity : 0 ≤ cPhi)).trans_eq
    dsimp [gaussianRaySize]
    ring
  · rw [gaussianTailRay, abs_mul, abs_of_nonneg (by dsimp [cPhi]; positivity)]
    apply (mul_le_mul_of_nonneg_left
      (show |psi b - 2 * psiFirst b| ≤ 3 * fullConstant 0 * exp (-t / 2) by linarith)
      (by dsimp [cPhi]; positivity : 0 ≤ cPhi)).trans_eq
    dsimp [gaussianTailSize]
    ring

private theorem exp_half_integrable :
    IntegrableOn (fun s : ℝ => exp (-s / 2)) (Ioi 0) := by
  convert integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0 using 1
  funext s
  congr 1
  ring

private theorem exp_half_tendsto :
    Tendsto (fun s : ℝ => exp (-s / 2)) atTop (𝓝 0) := by
  have h := tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (show (-1 / 2 : ℝ) < 0 by norm_num))
  convert h using 1 <;> ext s <;> dsimp only [Function.comp_apply, id_eq] <;> congr 1 <;> ring

private theorem gaussian_profile_l1 {a : ℝ} (ha : 0 ≤ a) :
    Integrable (actualGammaProfile (literalGaussian a)) := by
  rw [literalGaussian_actualProfile]
  change Integrable ((Ici (0 : ℝ)).indicator (fun t => (gaussianRay a t : ℂ)))
  apply (integrable_indicator_iff measurableSet_Ici).2
  apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
  apply (exp_half_integrable.const_mul gaussianRaySize).mono'
    (Complex.continuous_ofReal.comp (gaussianRay_continuous a)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
    (ray_bounds ha ht.le).1

private theorem gaussian_weighted_translate_integrable {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (exp (-(5 / 4 : ℝ) * s) : ℂ) *
      actualGammaProfile (literalGaussian a) (t + s)) (Ioi 0) := by
  rw [literalGaussian_actualProfile]
  have hc : Continuous (fun s : ℝ => (exp (-(5 / 4 : ℝ) * s) : ℂ) *
      (gaussianRay a (t + s) : ℂ)) :=
    (by fun_prop : Continuous (fun s : ℝ => (exp (-(5 / 4 : ℝ) * s) : ℂ))).mul
      (Complex.continuous_ofReal.comp ((gaussianRay_continuous a).comp (by fun_prop)))
  apply (exp_half_integrable.const_mul gaussianRaySize).mono'
    (hc.aestronglyMeasurable.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hs
      simp only [if_pos (by linarith : 0 ≤ t + s)]))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hts : 0 ≤ t + s := by linarith
  simp only [if_pos hts, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _)]
  calc
    exp (-(5 / 4 : ℝ) * s) * |gaussianRay a (t + s)| ≤
        1 * (gaussianRaySize * exp (-(t + s) / 2)) :=
      mul_le_mul (Real.exp_le_one_iff.mpr (by linarith))
        (ray_bounds ha hts).1 (abs_nonneg _) (by norm_num)
    _ ≤ gaussianRaySize * exp (-s / 2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (by linarith)) gaussianRaySize_nonneg

private theorem gaussianTailRay_deriv (a t : ℝ) :
    HasDerivAt (gaussianTailRay a)
      ((5 / 4 : ℝ) * gaussianTailRay a t - gaussianRay a t) t := by
  have hb : HasDerivAt (fun t : ℝ => a + t / 2) (1 / 2 : ℝ) t := by
    simpa using ((hasDerivAt_id t).div_const 2).const_add a
  convert ((((hasDerivAt_psi (a + t / 2)).comp t hb).sub
    (((hasDerivAt_psiFirst (a + t / 2)).comp t hb).const_mul 2)).const_mul cPhi) using 1
  · rfl
  · rw [psiSecond_eq, ← romikPhi_eq_source]
    dsimp only [gaussianTailRay, gaussianRay]
    ring

private theorem literalGaussian_right_tail {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    rightExponentialTail (5 / 4) (actualGammaProfile (literalGaussian a)) t =
      (gaussianTailRay a t : ℂ) := by
  let V : ℝ → ℂ := fun s =>
    (exp (-(5 / 4 : ℝ) * s) : ℂ) * (gaussianTailRay a (t + s) : ℂ)
  let U : ℝ → ℂ := fun s => (exp (-(5 / 4 : ℝ) * s) : ℂ) *
    actualGammaProfile (literalGaussian a) (t + s)
  have hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt V (-U s) s := by
    intro s hs
    have hts : 0 ≤ t + s := by linarith [hs.out]
    have he : HasDerivAt (fun s : ℝ => exp (-(5 / 4 : ℝ) * s))
        (-(5 / 4 : ℝ) * exp (-(5 / 4 : ℝ) * s)) s := by
      convert (((hasDerivAt_id s).const_mul (-(5 / 4 : ℝ))).exp) using 1 <;>
        dsimp only [Function.comp_apply, id_eq] <;> ring
    have hv := (gaussianTailRay_deriv a (t + s)).comp s ((hasDerivAt_id s).const_add t)
    convert he.ofReal_comp.mul hv.ofReal_comp using 1
    · rfl
    · dsimp only [U]
      simp only [literalGaussian_actualProfile, if_pos hts, Function.comp_apply]
      push_cast
      ring
  have htop : Tendsto V atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun s : ℝ => gaussianTailSize * exp (-s / 2))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have hts : 0 ≤ t + s := by linarith
      dsimp only [V]
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      calc
        exp (-(5 / 4 : ℝ) * s) * |gaussianTailRay a (t + s)| ≤
            1 * (gaussianTailSize * exp (-(t + s) / 2)) :=
          mul_le_mul (Real.exp_le_one_iff.mpr (by linarith))
            (ray_bounds ha hts).2 (abs_nonneg _) (by norm_num)
        _ ≤ gaussianTailSize * exp (-s / 2) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_left
            (exp_le_exp.mpr (by linarith)) gaussianTailSize_nonneg
    · simpa only [mul_zero] using exp_half_tendsto.const_mul gaussianTailSize
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (gaussian_weighted_translate_integrable ha ht).neg htop
  change (∫ s : ℝ in Ioi 0, U s) = _
  rw [integral_neg] at hFTC
  simpa only [V, zero_mul, mul_zero, exp_zero, Complex.ofReal_one, one_mul,
    add_zero, zero_sub, neg_inj] using hFTC

/-- The literal physical Gaussian has the displayed actual even B image.
The actual profile and every translated tail integral are genuinely L1;
the conclusion is an identity of the original source operators. -/
theorem actual_gaussian_suzuki_evenB {a : ℝ} (ha : 0 ≤ a) :
    Integrable (actualGammaProfile (fun x : ℝ =>
      (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ))) ∧
    (∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun s : ℝ => (exp (-(5 / 4 : ℝ) * s) : ℂ) *
        actualGammaProfile (fun x : ℝ =>
          (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ)) (t + s)) (Ioi 0)) ∧
    ∀ r : ℝ, actualSuzukiEvenBProfile (fun x : ℝ =>
        (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ)) r =
      (((Real.pi ^ (1 / 4 : ℝ) / 4) * romikPhi (a + |r|) : ℝ) : ℂ) := by
  refine ⟨gaussian_profile_l1 ha, (fun t ht => gaussian_weighted_translate_integrable ha ht), ?_⟩
  intro r
  change actualSuzukiBProfile (literalGaussian a) (2 * |r|) = _
  rw [actualSuzukiBProfile, literalGaussian_right_tail ha (by positivity),
    literalGaussian_actualProfile]
  simp only [if_pos (by positivity : 0 ≤ 2 * |r|)]
  dsimp only [gaussianRay, gaussianTailRay, cPhi]
  rw [show a + 2 * |r| / 2 = a + |r| by ring]
  push_cast
  ring

#print axioms actual_gaussian_suzuki_evenB

end D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile
