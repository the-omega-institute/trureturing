/- GID: D5/S3/Analytic/Fourier/ThetaCuspApproximation
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/ThetaCuspApproximation
   mirror-E: none(waiver:infinite-analytic-approximation)
   anchors: []
   utility: none
   digest: Compact theta cusp approximations with uniform weighted jets and shift bounds. -/

import D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
import D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed
import D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.RealDeriv
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-!
# Compact approximation of the complete shifted theta cusp

   Actual construction: first convolve Phi(a+|.|) with the normalized even
   bump of radius 1/(n+1), then multiply by a fixed bump at scale n+1.
   C-infinity comes from Mathlib's compact smooth convolution theorem.
   The Cusp theorem is used for its exact second derivative, including
   2*Phi'(a)*b_n. The density's derivatives are never used to bound that
   second derivative: their norms would diverge as its radius shrinks.

   Only the existing half-strip jet budget is consumed. In particular,
   there is no support-radius-dependent exp(R/2) substitution.
   Open-private imports reuse the source-owned cusp estimates verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Fourier.ThetaCuspApproximation

open Real Set MeasureTheory Filter
open scoped Topology ContDiff Convolution
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity

open private fullConstant fullConstant_nonneg evenPhi evenPhiJet jet
  jet_bound jet_decay evenPhiJet_continuous evenPhi_lipschitz
  firstJet firstJet_measurable evenPhi_deriv_off_zero
  hasDerivAt_mulConv_of_lipschitz mulConv cuspCharge
  evenPhi_mulConv_C2 from
  D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
open private actual_fullJet_zero_eq_phi_all actual_fullJet_eq_phi_iterated_all from
  D5.S3.Analytic.Fourier.ThetaRadialCurvature

private def cPhi : ℝ := Real.pi ^ (1 / 4 : ℝ) / 4

private def width (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem width_pos (n : ℕ) : 0 < width n := by
  dsimp [width]
  positivity

private theorem width_le_one (n : ℕ) : width n ≤ 1 := by
  dsimp [width]
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

private def smoothingBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  radiusBump (width n) (width_pos n)

private def density (n : ℕ) : ℝ → ℝ := (smoothingBump n).normed volume

private theorem density_support (n : ℕ) {x : ℝ} (hx : density n x ≠ 0) :
    |x| ≤ 1 := by
  have hs : x ∈ Metric.ball (0 : ℝ) (width n) := by
    have hs : x ∈ Function.support (density n) := hx
    rw [density, (smoothingBump n).support_normed_eq] at hs
    simpa only [smoothingBump, radiusBump] using hs
  have hlt : |x| < width n := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs
  exact hlt.le.trans (width_le_one n)

/-- The smoothing keeps the literal full theta cusp. -/
private def smoothed (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, evenPhi a (x - y) * density n y

private theorem smoothed_eq_convolution (a : ℝ) (n : ℕ) :
    smoothed a n =
      (density n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] evenPhi a) := by
  funext x
  change (∫ y : ℝ, evenPhi a (x-y) * density n y) =
    ∫ y : ℝ, density n y * evenPhi a (x-y)
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

private theorem smoothed_smooth (a : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (smoothed a n) := by
  rw [smoothed_eq_convolution]
  exact (smoothingBump n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (smoothingBump n).contDiff_normed
    (evenPhiJet_continuous a 0).locallyIntegrable

private theorem smoothed_even (a : ℝ) (n : ℕ) (x : ℝ) :
    smoothed a n (-x) = smoothed a n x := by
  rw [smoothed_eq_convolution]
  apply convolution_neg_of_neg_eq (ContinuousLinearMap.lsmul ℝ ℝ)
  · exact Eventually.of_forall fun y => (smoothingBump n).normed_neg y
  · exact Eventually.of_forall fun y => by
      simp only [evenPhi, evenPhiJet, abs_neg]

private theorem smoothed_first {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : ℝ) :
    deriv (smoothed a n) x =
      ∫ y : ℝ, firstJet a (x-y) * density n y := by
  have h := hasDerivAt_mulConv_of_lipschitz
    (evenPhi_lipschitz ha)
    (fun z => jet_bound ha 0 (abs_nonneg z))
    (firstJet_measurable a) (evenPhi_deriv_off_zero a)
    (smoothingBump n).integrable_normed x
  exact h.2.deriv

private theorem smoothed_second {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : ℝ) :
    deriv (deriv (smoothed a n)) x =
      (∫ y : ℝ, evenPhiJet a 2 (x-y) * density n y) +
        2 * cuspCharge a * density n x := by
  exact (evenPhi_mulConv_C2 ha (smoothingBump n).integrable_normed
    (smoothingBump n).continuous_normed).2 x

/- A consumed specialized envelope: normalized compact smoothing of the
   actual exponentially decaying jets. This avoids a general weighted
   convolution development. -/
private theorem density_convolution_envelope
    {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : Measurable f)
    (hbound : ∀ x, |f x| ≤ C * exp (-|x|)) (n : ℕ) (x : ℝ) :
    |∫ y : ℝ, f (x-y) * density n y| ≤
      (exp 1 * C) * exp (-|x|) := by
  let A := (exp 1 * C) * exp (-|x|)
  have hb := (smoothingBump n).integrable_normed (μ := volume)
  have hn (y : ℝ) : 0 ≤ density n y := (smoothingBump n).nonneg_normed y
  have hm (y : ℝ) : |f (x-y)| * density n y ≤ A * density n y := by
    by_cases hy : density n y = 0
    · simp [hy]
    · have hy1 := density_support n hy
      have htri : |x| ≤ |x-y| + |y| := by
        simpa only [sub_add_cancel] using abs_add_le (x-y) y
      have he : exp (-|x-y|) ≤ exp 1 * exp (-|x|) := by
        rw [← exp_add]
        exact exp_le_exp.mpr (by linarith)
      apply mul_le_mul_of_nonneg_right ?_ (hn y)
      calc
        _ ≤ C * (exp 1 * exp (-|x|)) :=
          (hbound _).trans (mul_le_mul_of_nonneg_left he hC)
        _ = A := by dsimp [A]; ring
  have hfi : Integrable (fun y : ℝ => f (x-y) * density n y) := by
    apply hb.bdd_mul (c := C)
      (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (hbound _).trans (mul_le_of_le_one_right hC
      (exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))))
  calc
    _ ≤ ∫ y : ℝ, |f (x-y)| * density n y := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn _)] using
        norm_integral_le_integral_norm (fun y : ℝ => f (x-y) * density n y)
    _ ≤ ∫ y : ℝ, A * density n y := by
      apply integral_mono
      · simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn _)] using hfi.norm
      · exact hb.const_mul A
      · exact hm
    _ = A := by
      rw [integral_const_mul]
      simp only [density, (smoothingBump n).integral_normed, mul_one]

private def jetEnvelope (k : ℕ) : ℝ := exp 1 * fullConstant k

private theorem jetEnvelope_nonneg (k : ℕ) : 0 ≤ jetEnvelope k :=
  mul_nonneg (exp_pos _).le (fullConstant_nonneg k)

private theorem smoothed_zeroth_bound {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : ℝ) :
    |smoothed a n x| ≤ jetEnvelope 0 * exp (-|x|) := by
  exact density_convolution_envelope (f := evenPhi a) (fullConstant_nonneg 0)
    (evenPhiJet_continuous a 0).measurable
    (fun y : ℝ => by simpa only [evenPhi, evenPhiJet, Real.norm_eq_abs] using
      (jet_decay (a := a) (x := |y|) ha 0 (abs_nonneg y))) n x

private theorem smoothed_first_bound {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : ℝ) :
    |deriv (smoothed a n) x| ≤ jetEnvelope 1 * exp (-|x|) := by
  rw [smoothed_first ha]
  apply density_convolution_envelope (fullConstant_nonneg 1) (firstJet_measurable a)
    (fun y : ℝ => ?_) n x
  by_cases hy : 0 ≤ y
  · simpa only [firstJet, if_pos hy, abs_of_nonneg hy, Real.norm_eq_abs] using
      jet_decay ha 1 hy
  · have hy0 : y < 0 := lt_of_not_ge hy
    simpa only [firstJet, if_neg hy, abs_of_neg hy0, abs_neg, Real.norm_eq_abs] using
      jet_decay ha 1 (neg_nonneg.mpr hy0.le)

private theorem smoothed_second_bound {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : ℝ) :
    |deriv (deriv (smoothed a n)) x| ≤
      jetEnvelope 2 * exp (-|x|) + 2 * |cuspCharge a| * density n x := by
  rw [smoothed_second ha]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact density_convolution_envelope (f := evenPhiJet a 2) (fullConstant_nonneg 2)
      (evenPhiJet_continuous a 2).measurable
      (fun y : ℝ => by simpa only [evenPhiJet, Real.norm_eq_abs] using
        (jet_decay (a := a) (x := |y|) ha 2 (abs_nonneg y))) n x
  · have hd : 0 ≤ density n x := (smoothingBump n).nonneg_normed x
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hd]

private def baseCutoff : ContDiffBump (0 : ℝ) := radiusBump 2 (by norm_num)
private def cutoff (n : ℕ) (x : ℝ) : ℝ := baseCutoff (width n * x)

private theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  baseCutoff.contDiff.comp (contDiff_const.mul contDiff_id)

private theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  have heq : cutoff n = (baseCutoff : ℝ → ℝ) ∘
      (Homeomorph.mulLeft₀ (width n) (width_pos n).ne') := rfl
  rw [heq]
  exact baseCutoff.hasCompactSupport.comp_homeomorph _

private theorem cutoff_bound (n : ℕ) (x : ℝ) : |cutoff n x| ≤ 1 := by
  change |baseCutoff (width n*x)| ≤ 1
  rw [abs_of_nonneg baseCutoff.nonneg]
  exact baseCutoff.le_one

private theorem cutoff_even (n : ℕ) (x : ℝ) : cutoff n (-x) = cutoff n x := by
  dsimp only [cutoff]
  rw [mul_neg, baseCutoff.neg]

private theorem base_cutoff_jet_bounds :
    ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
      (∀ x, |deriv (baseCutoff : ℝ → ℝ) x| ≤ D1) ∧
      (∀ x, |deriv (deriv (baseCutoff : ℝ → ℝ)) x| ≤ D2) := by
  have h1 : ContDiff ℝ ∞ (deriv (baseCutoff : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp baseCutoff.contDiff).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv (baseCutoff : ℝ → ℝ))) :=
    (contDiff_infty_iff_deriv.mp h1).2
  obtain ⟨B1, hB1⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    h1.continuous.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    h2.continuous.continuousOn
  refine ⟨|B1|, |B2|, abs_nonneg _, abs_nonneg _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Icc (-2 : ℝ) 2
    · exact (hB1 x hx).trans (le_abs_self _)
    · have hsup : tsupport (deriv (baseCutoff : ℝ → ℝ)) ⊆ Icc (-2 : ℝ) 2 := by
        apply tsupport_deriv_subset.trans
        simpa only [baseCutoff, ContDiffBump.tsupport_eq, radiusBump,
          Real.closedBall_eq_Icc, zero_sub, zero_add] using
          (Subset.rfl : Metric.closedBall (0 : ℝ) 2 ⊆ Metric.closedBall (0 : ℝ) 2)
      have hz : deriv (baseCutoff : ℝ → ℝ) x = 0 := by
        by_contra hn
        exact hx (hsup (subset_tsupport _ hn))
      simp only [hz, abs_zero]
      exact abs_nonneg _
  · intro x
    by_cases hx : x ∈ Icc (-2 : ℝ) 2
    · exact (hB2 x hx).trans (le_abs_self _)
    · have hsup : tsupport (deriv (deriv (baseCutoff : ℝ → ℝ))) ⊆ Icc (-2 : ℝ) 2 := by
        apply tsupport_deriv_subset.trans
        apply tsupport_deriv_subset.trans
        simpa only [baseCutoff, ContDiffBump.tsupport_eq, radiusBump,
          Real.closedBall_eq_Icc, zero_sub, zero_add] using
          (Subset.rfl : Metric.closedBall (0 : ℝ) 2 ⊆ Metric.closedBall (0 : ℝ) 2)
      have hz : deriv (deriv (baseCutoff : ℝ → ℝ)) x = 0 := by
        by_contra hn
        exact hx (hsup (subset_tsupport _ hn))
      simp only [hz, abs_zero]
      exact abs_nonneg _

private theorem cutoff_first (n : ℕ) (x : ℝ) :
    deriv (cutoff n) x = deriv (baseCutoff : ℝ → ℝ) (width n*x) * width n := by
  change deriv (fun y : ℝ => baseCutoff (width n * y)) x = _
  have hc : ContDiff ℝ ∞ (baseCutoff : ℝ → ℝ) := baseCutoff.contDiff
  simpa only [Function.comp_def, id_eq, mul_one] using
    (((hc.differentiable (by simp)) _).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul (width n))).deriv

private theorem cutoff_second (n : ℕ) (x : ℝ) :
    deriv (deriv (cutoff n)) x =
      deriv (deriv (baseCutoff : ℝ → ℝ)) (width n*x) * (width n)^2 := by
  have heq : deriv (cutoff n) = fun y =>
      deriv (baseCutoff : ℝ → ℝ) (width n*y) * width n := funext (cutoff_first n)
  rw [heq]
  have h1 : ContDiff ℝ ∞ (deriv (baseCutoff : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp baseCutoff.contDiff).2
  have hd := ((((h1.differentiable (by simp)) _).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul (width n))).mul_const (width n)).deriv
  simpa only [Function.comp_def, id_eq, mul_one, mul_assoc, pow_two] using hd

private theorem cutoff_jet_bounds {D1 D2 : ℝ} (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (h1 : ∀ x, |deriv (baseCutoff : ℝ → ℝ) x| ≤ D1)
    (h2 : ∀ x, |deriv (deriv (baseCutoff : ℝ → ℝ)) x| ≤ D2)
    (n : ℕ) (x : ℝ) :
    |deriv (cutoff n) x| ≤ D1 ∧ |deriv (deriv (cutoff n)) x| ≤ D2 := by
  constructor
  · rw [cutoff_first, abs_mul, abs_of_pos (width_pos n)]
    exact (mul_le_mul_of_nonneg_right (h1 _) (width_pos n).le).trans
      (mul_le_of_le_one_right hD1 (width_le_one n))
  · rw [cutoff_second, abs_mul, abs_of_nonneg (sq_nonneg (width n))]
    exact (mul_le_mul_of_nonneg_right (h2 _) (sq_nonneg _)).trans
      (mul_le_of_le_one_right hD2 (by
        nlinarith [width_pos n, width_le_one n]))

private def cutSmoothed (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  cutoff n x * smoothed a n x

private theorem cutSmoothed_smooth (a : ℝ) (n : ℕ) : ContDiff ℝ ∞ (cutSmoothed a n) :=
  (cutoff_smooth n).mul (smoothed_smooth a n)

/-- The actual compact even smooth approximation, with the original cPhi. -/
def gaussianCuspApproximation (a : ℝ) (n : ℕ) : WeilTestFunction where
  toFun x := ((cPhi * cutSmoothed a n x : ℝ) : ℂ)
  contDiff' := Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (cutSmoothed_smooth a n))
  hasCompactSupport' := by
    have hk : HasCompactSupport (cutSmoothed a n) := (cutoff_compact n).mul_right
    have hc : HasCompactSupport (fun x => cPhi * cutSmoothed a n x) := hk.mul_left
    exact hc.comp_left Complex.ofReal_zero
  even' x := by
    simp only [cutSmoothed, cutoff_even, smoothed_even]

private theorem approximation_bound {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : ℝ) :
    ‖gaussianCuspApproximation a n x‖ ≤
      (|cPhi| * jetEnvelope 0) * exp (-|x|) := by
  change ‖((cPhi * (cutoff n x * smoothed a n x) : ℝ) : ℂ)‖ ≤ _
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |cPhi| * (1 * (jetEnvelope 0 * exp (-|x|))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (cutoff_bound n x) (smoothed_zeroth_bound ha n x)
          (abs_nonneg _) zero_le_one) (abs_nonneg _)
    _ = _ := by ring

private theorem exponential_half_integrable :
    Integrable (fun x : ℝ => exp (-|x|/2)) := by
  have hp : IntegrableOn (fun x : ℝ => exp (-|x|/2)) (Ioi 0) := by
    apply IntegrableOn.congr_fun
      (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 0) ?_
      measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos (show 0 < x from hx)]
    congr 1
    ring
  have hn : IntegrableOn (fun x : ℝ => exp (-|x|/2)) (Iic 0) := by
    apply IntegrableOn.congr_fun
      (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1/2) 0) ?_
      measurableSet_Iic
    intro x hx
    dsimp only
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using integrableOn_union.mpr ⟨hn, hp⟩

private def halfMass : ℝ := ∫ x : ℝ, exp (-|x|/2)

private theorem halfMass_nonneg : 0 ≤ halfMass :=
  integral_nonneg fun _ => (exp_pos _).le

private theorem weighted_density_bound (n : ℕ) :
    (∫ x : ℝ, exp (|x|/2) * density n x) ≤ exp (1/2 : ℝ) := by
  have hb : Integrable (density n) := (smoothingBump n).integrable_normed (μ := volume)
  have hwi : Integrable (fun x : ℝ => exp (|x|/2) * density n x) :=
    ((by fun_prop : Continuous (fun x : ℝ => exp (|x|/2))).mul
      (smoothingBump n).continuous_normed).integrable_of_hasCompactSupport
      (smoothingBump n).hasCompactSupport_normed.mul_left
  calc
    _ ≤ ∫ x : ℝ, exp (1/2 : ℝ) * density n x := by
      apply integral_mono hwi (hb.const_mul _)
      intro x
      by_cases hx : density n x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right
          (exp_le_exp.mpr (by linarith [density_support n hx]))
          ((smoothingBump n).nonneg_normed x)
    _ = exp (1/2 : ℝ) := by
      rw [integral_const_mul]
      simp only [density, (smoothingBump n).integral_normed, mul_one]

private theorem cutSmoothed_second (a : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (cutSmoothed a n)) x =
      deriv (deriv (cutoff n)) x * smoothed a n x +
        2 * deriv (cutoff n) x * deriv (smoothed a n) x +
          cutoff n x * deriv (deriv (smoothed a n)) x := by
  have hc := cutoff_smooth n
  have hu := smoothed_smooth a n
  have hc1 : ContDiff ℝ ∞ (deriv (cutoff n)) :=
    (contDiff_infty_iff_deriv.mp hc).2
  have hu1 : ContDiff ℝ ∞ (deriv (smoothed a n)) :=
    (contDiff_infty_iff_deriv.mp hu).2
  have heq : deriv (cutSmoothed a n) = fun y =>
      deriv (cutoff n) y * smoothed a n y +
        cutoff n y * deriv (smoothed a n) y := by
    funext y
    exact (((hc.differentiable (by simp)) y).hasDerivAt.mul
      (((hu.differentiable (by simp)) y).hasDerivAt)).deriv
  rw [heq]
  have hd :=
    ((((hc1.differentiable (by simp)) x).hasDerivAt.mul
      (((hu.differentiable (by simp)) x).hasDerivAt)).add
      ((((hc.differentiable (by simp)) x).hasDerivAt.mul
        (((hu1.differentiable (by simp)) x).hasDerivAt)))).deriv
  convert hd using 1 <;> ring

private theorem approximation_second (a : ℝ) (n : ℕ) (x : ℝ) :
    ((deriv^[2]) (gaussianCuspApproximation a n : ℝ → ℂ)) x =
      ((cPhi * deriv (deriv (cutSmoothed a n)) x : ℝ) : ℂ) := by
  have hk := cutSmoothed_smooth a n
  have hk1 : ContDiff ℝ ∞ (deriv (cutSmoothed a n)) :=
    (contDiff_infty_iff_deriv.mp hk).2
  have heq : deriv (gaussianCuspApproximation a n : ℝ → ℂ) =
      fun y => ((cPhi * deriv (cutSmoothed a n) y : ℝ) : ℂ) := by
    funext y
    exact ((((hk.differentiable (by simp)) y).hasDerivAt.const_mul cPhi).ofReal_comp).deriv
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [heq]
  exact ((((hk1.differentiable (by simp)) x).hasDerivAt.const_mul cPhi).ofReal_comp).deriv

private def secondEnvelope (D1 D2 : ℝ) : ℝ :=
  D2 * jetEnvelope 0 + 2 * D1 * jetEnvelope 1 + jetEnvelope 2

private theorem secondEnvelope_nonneg {D1 D2 : ℝ} (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) :
    0 ≤ secondEnvelope D1 D2 := by
  have h0 := jetEnvelope_nonneg 0
  have h1 := jetEnvelope_nonneg 1
  have h2 := jetEnvelope_nonneg 2
  dsimp only [secondEnvelope]
  positivity

private theorem cutSmoothed_second_bound {a : ℝ} (ha : 0 ≤ a)
    {D1 D2 : ℝ} (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (h1 : ∀ x, |deriv (baseCutoff : ℝ → ℝ) x| ≤ D1)
    (h2 : ∀ x, |deriv (deriv (baseCutoff : ℝ → ℝ)) x| ≤ D2)
    (n : ℕ) (x : ℝ) :
    |deriv (deriv (cutSmoothed a n)) x| ≤
      secondEnvelope D1 D2 * exp (-|x|) +
        2 * |cuspCharge a| * density n x := by
  obtain ⟨hc1, hc2⟩ := cutoff_jet_bounds hD1 hD2 h1 h2 n x
  have hu0 := smoothed_zeroth_bound ha n x
  have hu1 := smoothed_first_bound ha n x
  have hu2 := smoothed_second_bound ha n x
  have hb : 0 ≤ density n x := (smoothingBump n).nonneg_normed x
  rw [cutSmoothed_second]
  calc
    _ ≤ |deriv (deriv (cutoff n)) x * smoothed a n x| +
        |2 * deriv (cutoff n) x * deriv (smoothed a n) x| +
          |cutoff n x * deriv (deriv (smoothed a n)) x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ D2 * (jetEnvelope 0 * exp (-|x|)) +
        2 * D1 * (jetEnvelope 1 * exp (-|x|)) +
          (jetEnvelope 2 * exp (-|x|) + 2 * |cuspCharge a| * density n x) := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply add_le_add
      · exact add_le_add
          (mul_le_mul hc2 hu0 (abs_nonneg _) hD2)
          (mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by norm_num))
            hu1 (abs_nonneg _) (by positivity))
      · exact (mul_le_mul (cutoff_bound n x) hu2 (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
    _ = _ := by dsimp [secondEnvelope]; ring

private theorem approximation_budget {a : ℝ} (ha : 0 ≤ a)
    {D1 D2 : ℝ} (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (h1 : ∀ x, |deriv (baseCutoff : ℝ → ℝ) x| ≤ D1)
    (h2 : ∀ x, |deriv (deriv (baseCutoff : ℝ → ℝ)) x| ≤ D2)
    (n : ℕ) :
    closedStripJetBudget (gaussianCuspApproximation a n) (1/2) ≤
      |cPhi| * ((jetEnvelope 0 + secondEnvelope D1 D2) * halfMass +
        2 * |cuspCharge a| * exp (1/2 : ℝ)) := by
  let B := secondEnvelope D1 D2
  let J := 2 * |cuspCharge a|
  have hwd : Integrable (fun x : ℝ => exp (|x|/2) * density n x) :=
    ((by fun_prop : Continuous (fun x : ℝ => exp (|x|/2))).mul
      (smoothingBump n).continuous_normed).integrable_of_hasCompactSupport
      (smoothingBump n).hasCompactSupport_normed.mul_left
  have h0 : (∫ x : ℝ, exp ((1/2 : ℝ)*|x|) * ‖gaussianCuspApproximation a n x‖) ≤
      |cPhi| * jetEnvelope 0 * halfMass := by
    calc
      _ ≤ ∫ x : ℝ, (|cPhi| * jetEnvelope 0) * exp (-|x|/2) := by
        apply integral_mono_of_nonneg
          (Eventually.of_forall fun x => mul_nonneg (exp_pos _).le (norm_nonneg _))
          (exponential_half_integrable.const_mul _) (Eventually.of_forall fun x => ?_)
        calc
          _ ≤ exp ((1/2 : ℝ)*|x|) *
              ((|cPhi| * jetEnvelope 0)*exp (-|x|)) :=
            mul_le_mul_of_nonneg_left (approximation_bound ha n x) (exp_pos _).le
          _ = _ := by
            rw [show (1/2 : ℝ)*|x| = |x|/2 by ring]
            rw [show exp (|x|/2) * ((|cPhi| * jetEnvelope 0)*exp (-|x|)) =
                (|cPhi| * jetEnvelope 0)*(exp (|x|/2)*exp (-|x|)) by ring]
            rw [← exp_add]
            congr 2
            ring
      _ = _ := by rw [integral_const_mul]; rfl
  have hsecond : (∫ x : ℝ, exp ((1/2 : ℝ)*|x|) *
      ‖((deriv^[2]) (gaussianCuspApproximation a n : ℝ → ℂ)) x‖) ≤
      |cPhi| * (B * halfMass + J * exp (1/2 : ℝ)) := by
    have hmajor : Integrable (fun x : ℝ =>
        |cPhi| * (B*exp (-|x|/2) + J*(exp (|x|/2)*density n x))) :=
      ((exponential_half_integrable.const_mul B).add (hwd.const_mul J)).const_mul _
    calc
      _ ≤ ∫ x : ℝ, |cPhi| *
          (B*exp (-|x|/2) + J*(exp (|x|/2)*density n x)) := by
        apply integral_mono_of_nonneg
          (Eventually.of_forall fun x => mul_nonneg (exp_pos _).le (norm_nonneg _))
          hmajor (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [approximation_second, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        calc
          _ ≤ exp ((1/2 : ℝ)*|x|) * (|cPhi| *
              (B*exp (-|x|) + J*density n x)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (cutSmoothed_second_bound ha hD1 hD2 h1 h2 n x) (abs_nonneg _))
              (exp_pos _).le
          _ = _ := by
            rw [show (1/2 : ℝ)*|x| = |x|/2 by ring]
            have he : exp (|x|/2) * exp (-|x|) = exp (-|x|/2) := by
              rw [← exp_add]
              congr 1
              ring
            linear_combination (|cPhi| * B)*he
      _ = |cPhi| * (B*halfMass + J*(∫ x : ℝ, exp (|x|/2)*density n x)) := by
        rw [integral_const_mul,
          integral_add (exponential_half_integrable.const_mul B) (hwd.const_mul J),
          integral_const_mul, integral_const_mul]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (weighted_density_bound n)
          (by dsimp [J]; positivity))) (abs_nonneg _)
  unfold closedStripJetBudget
  exact (add_le_add h0 hsecond).trans_eq (by dsimp only [B, J]; ring)

private theorem width_tendsto : Tendsto width atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0)
  exact (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0))

private theorem smoothed_tendsto (a x : ℝ) :
    Tendsto (fun n => smoothed a n x) atTop (𝓝 (evenPhi a x)) := by
  have hp : Tendsto (fun n => (smoothingBump n).rOut) atTop (𝓝 0) := width_tendsto
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) hp (evenPhiJet_continuous a 0) x
  simpa only [smoothed_eq_convolution, density, evenPhi] using h

private theorem cutoff_tendsto (x : ℝ) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have hx := width_tendsto.mul_const x
  have h := baseCutoff.continuous.continuousAt.tendsto.comp hx
  have hz : baseCutoff (0 : ℝ) = 1 :=
    baseCutoff.one_of_mem_closedBall (by simp [baseCutoff, radiusBump])
  simpa only [cutoff, Function.comp_def, zero_mul, hz] using h

private theorem approximation_tendsto {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    Tendsto (fun n => gaussianCuspApproximation a n x) atTop
      (𝓝 (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (((cutoff_tendsto x).mul (smoothed_tendsto a x)).const_mul cPhi)
  change Tendsto (fun n => ((cPhi * cutSmoothed a n x : ℝ) : ℂ)) atTop
    (𝓝 (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ)))
  simpa only [Function.comp_def, cutSmoothed, one_mul,
    evenPhi, evenPhiJet, jet, actual_fullJet_zero_eq_phi_all] using h

private theorem target_bound {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    ‖(((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))‖ ≤
      (|cPhi| * fullConstant 0) * exp (-|x|) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h := jet_decay ha 0 (abs_nonneg x)
  simp only [jet, actual_fullJet_zero_eq_phi_all, Real.norm_eq_abs] at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (by ring)

private theorem approximation_weighted_L1_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n => ∫ x : ℝ, exp (|x|/2) *
      ‖gaussianCuspApproximation a n x -
        (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))‖) atTop (𝓝 0) := by
  let A := |cPhi| * jetEnvelope 0 + |cPhi| * fullConstant 0
  have htarget : Continuous (fun x : ℝ =>
      (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))) := by
    have heq : (fun x : ℝ => (((cPhi * romikPhi (a + |x|):ℝ):ℂ))) =
        fun x : ℝ => (((cPhi * evenPhi a x:ℝ):ℂ)) := by
      funext x
      simp only [evenPhi, evenPhiJet, jet, actual_fullJet_zero_eq_phi_all]
    rw [heq]
    exact Complex.continuous_ofReal.comp
      (continuous_const.mul (evenPhiJet_continuous a 0))
  have hweight : Continuous (fun x : ℝ => exp (|x|/2)) := by fun_prop
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x : ℝ => exp (|x|/2) *
      ‖gaussianCuspApproximation a n x -
        (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))‖) volume :=
    (hweight.mul
      (((gaussianCuspApproximation a n).continuous.sub htarget).norm)).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x : ℝ,
      ‖exp (|x|/2) * ‖gaussianCuspApproximation a n x -
        (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))‖‖ ≤ A*exp (-|x|/2) := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := (norm_sub_le _ _).trans
      (add_le_add (approximation_bound ha n x) (target_bound ha x))
    calc
      _ ≤ exp (|x|/2) * (A * exp (-|x|)) :=
        mul_le_mul_of_nonneg_left (hb.trans_eq (by dsimp [A]; ring)) (exp_pos _).le
      _ = _ := by
        rw [show exp (|x|/2) * (A*exp (-|x|)) =
            A*(exp (|x|/2)*exp (-|x|)) by ring, ← exp_add]
        congr 2
        ring
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun n => exp (|x|/2) *
      ‖gaussianCuspApproximation a n x -
        (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))‖) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    have hz : Tendsto (fun _ : ℕ => (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ)))
        atTop (𝓝 (((cPhi * romikPhi (a+|x|) : ℝ) : ℂ))) := tendsto_const_nhds
    have hx := ((approximation_tendsto ha x).sub hz).norm
    simpa only [sub_self, norm_zero, mul_zero] using hx.const_mul (exp (|x|/2))
  have hD := tendsto_integral_of_dominated_convergence
    (fun x : ℝ => A * exp (-|x|/2)) hmeas
    (exponential_half_integrable.const_mul A) hbound hlim
  simpa only [integral_zero] using hD

/-- One constant controls the actual compact even smooth approximation for
every nonnegative shift and every approximation index. Each shifted sequence
converges in weighted L1 to its literal Gaussian B profile. The exact cusp
jump is paid uniformly by the full first-jet bound; no RH or zero-set
assumption is used. -/
theorem actual_gaussian_cusp_compact_approximation :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : ℝ, 0 ≤ a →
      (∀ n : ℕ, closedStripJetBudget (gaussianCuspApproximation a n) (1/2) ≤ C) ∧
      Tendsto (fun n => ∫ x : ℝ, exp (|x|/2) *
        ‖gaussianCuspApproximation a n x -
          ((((Real.pi^(1/4 : ℝ)/4) * romikPhi (a+|x|) : ℝ) : ℂ))‖)
        atTop (𝓝 0) ∧
      (∀ n : ℕ, ∀ x : ℝ,
        ‖gaussianCuspApproximation a n x‖ ≤ C * exp (-|x|)) := by
  obtain ⟨D1, D2, hD1, hD2, h1, h2⟩ := base_cutoff_jet_bounds
  let B := |cPhi| * ((jetEnvelope 0 + secondEnvelope D1 D2) * halfMass +
    2 * fullConstant 1 * exp (1/2 : ℝ))
  let C := B + |cPhi| * jetEnvelope 0
  have hB : 0 ≤ B := by
    have h0 := jetEnvelope_nonneg 0
    have h2 := secondEnvelope_nonneg hD1 hD2
    have hmass := halfMass_nonneg
    have hcharge := fullConstant_nonneg 1
    dsimp only [B]
    positivity
  have hC : 0 ≤ C := add_nonneg hB (mul_nonneg (abs_nonneg _) (jetEnvelope_nonneg 0))
  refine ⟨C, hC, ?_⟩
  intro a ha
  have hcharge : |cuspCharge a| ≤ fullConstant 1 := by
    simpa only [cuspCharge, Real.norm_eq_abs] using
      (jet_bound (a := a) (x := (0 : ℝ)) ha 1 le_rfl)
  have hBmajor : |cPhi| *
      ((jetEnvelope 0 + secondEnvelope D1 D2) * halfMass +
        2 * |cuspCharge a| * exp (1/2 : ℝ)) ≤ B := by
    dsimp only [B]
    apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcharge (by norm_num)) (exp_pos _).le)
  refine ⟨?_, approximation_weighted_L1_tendsto ha, ?_⟩
  · intro n
    exact ((approximation_budget ha hD1 hD2 h1 h2 n).trans hBmajor).trans
      (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (jetEnvelope_nonneg 0)))
  · intro n x
    exact (approximation_bound ha n x).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (exp_pos _).le)

#print axioms actual_gaussian_cusp_compact_approximation

end D5.S3.Analytic.Fourier.ThetaCuspApproximation
