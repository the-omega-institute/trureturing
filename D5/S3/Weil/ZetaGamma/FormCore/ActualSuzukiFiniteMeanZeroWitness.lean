/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteMeanZeroWitness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: Actual mean-zero H6 sources with all Gamma domains and raw sixth-moment ratios arbitrarily close to one. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFinitePhysicalFeature
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy

open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology Function

private def meanZeroSeparatedFeature (κ : ℝ) (a : ℂ) (x : ℝ) : ℂ :=
  finitePhysicalFeature 0 κ x - a * finitePhysicalFeature 0 (κ / 4) x

private theorem meanZeroSeparatedFeature_center_ne {κ : ℝ} (hκ : 0 < κ) (a : ℂ) :
    meanZeroSeparatedFeature κ a (Real.pi * Real.exp (κ / 2)) ≠ 0 := by
  have hx : Real.pi ≤ Real.pi * Real.exp (κ / 2) := by
    have he : 1 ≤ Real.exp (κ / 2 : ℝ) :=
      Real.one_le_exp_iff.mpr (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hl : Real.log ((Real.pi * Real.exp (κ / 2)) / Real.pi) = (κ / 2 : ℝ) := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
  have hsmall : finitePhysicalFeature 0 (κ / 4) (Real.pi * Real.exp (κ / 2)) = 0 := by
    have hprof : finiteCompressedProfile 0 (κ / 4) (κ / 2) = 0 :=
      finiteCompressed_zero_off 0 (by positivity : (0 : ℝ) < κ / 4)
        (by intro h; have hu := h.2; linarith [hκ])
    simp only [finitePhysicalFeature, sourceOfProfile, if_pos hx, hl, hprof, mul_zero]
  simpa only [meanZeroSeparatedFeature, hsmall, mul_zero, sub_zero] using
    (finitePhysical_center_ne 0 hκ)

private theorem meanZeroSeparatedFeature_continuous {κ : ℝ} (hκ : 0 < κ) (a : ℂ) :
    Continuous (meanZeroSeparatedFeature κ a) :=
  (finitePhysical_continuous 0 hκ).sub
    (continuous_const.mul
      (finitePhysical_continuous 0 (by positivity : (0 : ℝ) < κ / 4)))

private theorem meanZeroSeparatedFeature_zero_le_pi {κ : ℝ} (hκ : 0 < κ) (a : ℂ) {x : ℝ}
    (hx : x ≤ Real.pi) : meanZeroSeparatedFeature κ a x = 0 := by
  simp only [meanZeroSeparatedFeature,
    finitePhysical_zero_le_pi 0 hκ hx,
    finitePhysical_zero_le_pi 0 (by positivity : (0 : ℝ) < κ / 4) hx,
    mul_zero, sub_self]

private theorem meanZeroSeparatedFeature_support {κ : ℝ} (hκ : 0 < κ) (a : ℂ) :
    Function.support (meanZeroSeparatedFeature κ a) ⊆
      Icc Real.pi (Real.pi * Real.exp (3 * κ / 4)) := by
  intro x hx
  by_contra hn
  have hlarge : finitePhysicalFeature 0 κ x = 0 := by
    by_contra h
    exact hn (by simpa only [mul_one] using
      finitePhysical_support 0 hκ h)
  have hsmall : finitePhysicalFeature 0 (κ / 4) x = 0 := by
    by_contra h
    have hs := finitePhysical_support 0 (by positivity : (0 : ℝ) < κ / 4) h
    apply hn
    refine ⟨hs.1, hs.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact Real.exp_le_exp.mpr (by linarith [hκ])
  exact hx (by simp only [meanZeroSeparatedFeature, hlarge, hsmall, mul_zero, sub_self])

private theorem meanZeroSeparatedFeature_compact {κ : ℝ} (hκ : 0 < κ) (a : ℂ) :
    HasCompactSupport (meanZeroSeparatedFeature κ a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (meanZeroSeparatedFeature_support hκ a)

private theorem meanZeroSeparatedFeature_density_compact {κ : ℝ} (hκ : 0 < κ) (a : ℂ) (w : ℝ → ℝ) :
    HasCompactSupport (fun x : ℝ => w x * ‖meanZeroSeparatedFeature κ a x‖ ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.pi) (b := Real.pi * Real.exp (3 * κ / 4)))
  intro x hx
  by_contra hn
  have hz : meanZeroSeparatedFeature κ a x = 0 := by
    by_contra h
    exact hn (meanZeroSeparatedFeature_support hκ a h)
  exact hx (by simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero])

private theorem meanZeroSeparatedFeature_h6 {κ : ℝ} (hκ : 0 < κ) (a : ℂ) :
    originalPhysicalH6 (meanZeroSeparatedFeature κ a) := by
  refine ⟨?_, ?_⟩
  · exact ((meanZeroSeparatedFeature_continuous hκ a).memLp_of_hasCompactSupport
      (meanZeroSeparatedFeature_compact hκ a)).mono_measure Measure.restrict_le_self
  · have hc : Continuous (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
        ‖meanZeroSeparatedFeature κ a x‖ ^ 2) :=
      ((continuous_id.div_const Real.pi).pow 6).mul
        ((meanZeroSeparatedFeature_continuous hκ a).norm.pow 2)
    exact (hc.integrable_of_hasCompactSupport
      (meanZeroSeparatedFeature_density_compact hκ a _)).integrableOn

private theorem meanZeroSeparatedFeature_excess_pos {κ : ℝ} (hκ : 0 < κ) (a : ℂ) :
    0 < ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖meanZeroSeparatedFeature κ a x‖ ^ 2 := by
  let d : ℝ → ℝ := fun x =>
    ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖meanZeroSeparatedFeature κ a x‖ ^ 2
  have hd : Continuous d :=
    (((continuous_id.div_const Real.pi).pow 6).sub continuous_const).mul
      ((meanZeroSeparatedFeature_continuous hκ a).norm.pow 2)
  have hi : Integrable d volume := hd.integrable_of_hasCompactSupport
    (meanZeroSeparatedFeature_density_compact hκ a _)
  have hnn (x : ℝ) : 0 ≤ d x := by
    by_cases hx : x ≤ Real.pi
    · simp only [d, meanZeroSeparatedFeature_zero_le_pi hκ a hx, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · have hratio : 1 ≤ x / Real.pi :=
        (le_div_iff₀ Real.pi_pos).2 (by linarith [le_of_not_ge hx])
      exact mul_nonneg (sub_nonneg.2 (one_le_pow₀ hratio)) (sq_nonneg _)
  have hwhole : (∫ x : ℝ in Ioi Real.pi, d x) = ∫ x : ℝ, d x := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ioi Real.pi
    · simp only [Set.indicator_of_mem hx]
    · simp only [d, meanZeroSeparatedFeature_zero_le_pi hκ a (le_of_not_gt hx),
        norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        Set.indicator_of_notMem hx]
  change 0 < ∫ x : ℝ in Ioi Real.pi, d x
  rw [hwhole]
  apply integral_pos_of_integrable_nonneg_nonzero hd hi hnn
    (x := Real.pi * Real.exp (κ / 2))
  have hratio : 1 < (Real.pi * Real.exp (κ / 2)) / Real.pi := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  let y : ℝ := (Real.pi * Real.exp (κ / 2)) / Real.pi
  have hy : 1 < y := hratio
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hweight : 0 < y ^ (6 : ℕ) - 1 := by
    rw [show y ^ (6 : ℕ) - 1 =
      (y - 1) * (y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1) by ring]
    exact mul_pos (sub_pos.2 hy) (by positivity)
  apply ne_of_gt
  exact mul_pos hweight (pow_pos
    (norm_pos_iff.mpr (meanZeroSeparatedFeature_center_ne hκ a)) 2)

private theorem meanZeroSeparatedFeature_fullHasSum {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (a : ℂ) {x : ℝ}
    (hx : Real.pi ≤ x) :
    HasSum (fun k : ℕ => physicalTerm (meanZeroSeparatedFeature κ a) k x)
      (meanZeroSeparatedFeature κ a x) := by
  have hlarge := finitePhysical_fullHasSum 0
    hκ hκ1 hx
  have hsmall := finitePhysical_fullHasSum 0
    (by positivity : (0 : ℝ) < κ / 4) (by linarith : κ / 4 ≤ 1) hx
  convert hlarge.sub (hsmall.mul_left a) using 1
  · funext k
    simp only [meanZeroSeparatedFeature, physicalTerm]
    ring
  · rfl

private theorem meanZeroSeparatedFeature_actualProfile_eq {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (a : ℂ) :
    actualGammaProfile (meanZeroSeparatedFeature κ a) =
      fun t : ℝ => finiteCompressedProfile 0 κ t -
        a * finiteCompressedProfile 0 (κ / 4) t := by
  have hlarge := finitePhysical_actualProfile_eq 0
    hκ hκ1
  have hsmall := finitePhysical_actualProfile_eq 0
    (by positivity : (0 : ℝ) < κ / 4) (by linarith : κ / 4 ≤ 1)
  funext t
  calc
    actualGammaProfile (meanZeroSeparatedFeature κ a) t =
        actualGammaProfile (finitePhysicalFeature 0 κ) t -
          a * actualGammaProfile (finitePhysicalFeature 0 (κ / 4)) t := by
      by_cases ht : 0 ≤ t
      · have hx : Real.pi ≤ Real.pi * Real.exp t := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (Real.one_le_exp_iff.mpr ht) Real.pi_pos.le
        have hc := (meanZeroSeparatedFeature_fullHasSum hκ hκ1 a hx).tsum_eq
        have hl := (finitePhysical_fullHasSum 0
          hκ hκ1 hx).tsum_eq
        have hs := (finitePhysical_fullHasSum 0
          (by positivity : (0 : ℝ) < κ / 4) (by linarith : κ / 4 ≤ 1) hx).tsum_eq
        simp only [actualGammaProfile, if_pos ht, fullTheta, hc, hl, hs, meanZeroSeparatedFeature]
        ring
      · simp only [actualGammaProfile, if_neg ht, mul_zero, sub_self]
    _ = _ := by rw [hlarge, hsmall]

private theorem meanZeroFiniteProfile_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (finiteCompressedProfile 0 κ) volume := by
  have hs : HasCompactSupport (finiteCompressedProfile 0 κ) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra hn
    exact ht (finiteCompressed_zero_off 0 hκ hn)
  exact (finiteCompressed_continuous 0 κ).integrable_of_hasCompactSupport hs

private theorem meanZeroFiniteProfile_continuous_mul_integrable {κ : ℝ} (hκ : 0 < κ)
    (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable (fun t : ℝ => g t * finiteCompressedProfile 0 κ t) volume := by
  have hs : HasCompactSupport
      (fun t : ℝ => g t * finiteCompressedProfile 0 κ t) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra hn
    exact ht (by
      change g t * finiteCompressedProfile 0 κ t = 0
      rw [finiteCompressed_zero_off 0 hκ hn, mul_zero])
  exact (hg.mul (finiteCompressed_continuous 0 κ)).integrable_of_hasCompactSupport hs

private theorem meanZeroFiniteProfile_phase_integrable {κ : ℝ} (hκ : 0 < κ) (ξ : ℝ) :
    Integrable (fun t : ℝ => sourcePhase ξ t * finiteCompressedProfile 0 κ t) volume := by
  apply meanZeroFiniteProfile_continuous_mul_integrable hκ
  show Continuous (fun t : ℝ => sourcePhase ξ t)
  unfold sourcePhase
  fun_prop

private theorem meanZeroSeparatedFeature_fourier {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (a : ℂ) (ξ : ℝ) :
    unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature κ a)) ξ =
      unitarySourceFourier (finiteCompressedProfile 0 κ) ξ -
        a * unitarySourceFourier (finiteCompressedProfile 0 (κ / 4)) ξ := by
  rw [meanZeroSeparatedFeature_actualProfile_eq hκ hκ1 a]
  simp only [unitarySourceFourier_eq_integral]
  rw [show (fun t : ℝ => sourcePhase ξ t *
        (finiteCompressedProfile 0 κ t - a * finiteCompressedProfile 0 (κ / 4) t)) =
      (fun t : ℝ => sourcePhase ξ t * finiteCompressedProfile 0 κ t -
        a * (sourcePhase ξ t * finiteCompressedProfile 0 (κ / 4) t)) from
      funext fun t => by ring,
    integral_sub
      (meanZeroFiniteProfile_phase_integrable hκ ξ)
      ((meanZeroFiniteProfile_phase_integrable (by positivity : (0 : ℝ) < κ / 4) ξ).const_mul a),
    integral_const_mul]
  ring

private theorem meanZeroSeparatedFeature_in_all_shift_domains {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (a : ℂ) (c : ℝ) :
    originalGammaFormDomain c (meanZeroSeparatedFeature κ a) := by
  have hc (κ : ℝ) (hκ : 0 < κ) :
      Continuous (unitarySourceFourier (finiteCompressedProfile 0 κ)) := by
    unfold unitarySourceFourier
    exact continuous_const.mul
      ((Zeta23.EF.continuous_fourier_of_integrable
        (meanZeroFiniteProfile_integrable hκ)).comp (by fun_prop))
  have hfreq : Continuous
      (unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature κ a))) := by
    convert (hc κ hκ).sub
      (continuous_const.mul (hc (κ / 4) (by positivity))) using 1
    funext ξ
    exact meanZeroSeparatedFeature_fourier hκ hκ1 a ξ
  have hlarge := finiteCompressed_all_shift_integrable 0
    hκ |c|
  have hsmall := finiteCompressed_all_shift_integrable 0
    (by positivity : (0 : ℝ) < κ / 4) |c|
  unfold originalGammaFormDomain
  apply ((hlarge.add (hsmall.const_mul (‖a‖ ^ 2))).const_mul 2).mono'
    (((Symbol.finiteGammaWeight_continuous.add continuous_const).mul
      (hfreq.norm.pow 2)).aestronglyMeasurable)
  filter_upwards with ξ
  have hg0 : 0 ≤ Symbol.gammaWeight ξ :=
    (by linarith [(Symbol.actualGammaWeight_bounds ξ).1])
  have hg : |Symbol.gammaWeight ξ + c| ≤ Symbol.gammaWeight ξ + |c| := by
    calc
      _ ≤ |Symbol.gammaWeight ξ| + |c| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg hg0]
  have hsq :
      ‖unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature κ a)) ξ‖ ^ 2 ≤
        2 * ‖unitarySourceFourier (finiteCompressedProfile 0 κ) ξ‖ ^ 2 +
        2 * ‖a‖ ^ 2 * ‖unitarySourceFourier (finiteCompressedProfile 0 (κ / 4)) ξ‖ ^ 2 := by
    rw [meanZeroSeparatedFeature_fourier hκ hκ1 a]
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_le (unitarySourceFourier (finiteCompressedProfile 0 κ) ξ)
        (a * unitarySourceFourier (finiteCompressedProfile 0 (κ / 4)) ξ)) 2
    rw [norm_mul] at h
    nlinarith only [h, sq_nonneg
      (‖unitarySourceFourier (finiteCompressedProfile 0 κ) ξ‖ -
        ‖a‖ * ‖unitarySourceFourier (finiteCompressedProfile 0 (κ / 4)) ξ‖)]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg
      ‖unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature κ a)) ξ‖)]
  calc
    _ ≤ (Symbol.gammaWeight ξ + |c|) *
        ‖unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature κ a)) ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hg (sq_nonneg _)
    _ ≤ (Symbol.gammaWeight ξ + |c|) *
        (2 * ‖unitarySourceFourier (finiteCompressedProfile 0 κ) ξ‖ ^ 2 +
          2 * ‖a‖ ^ 2 * ‖unitarySourceFourier (finiteCompressedProfile 0 (κ / 4)) ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (add_nonneg hg0 (abs_nonneg c))
    _ = _ := by ring

open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

private def meanZeroActualMean (F : ℝ → ℂ) : ℂ :=
  ∫ r : ℝ, actualSuzukiEvenBProfile F r

private theorem meanZeroEvenDouble_l1_mass (b : ℝ → ℂ)
    (hb : IntegrableOn b (Ioi (0 : ℝ))) :
    Integrable (fun r : ℝ => b (2 * |r|)) volume ∧
      (∫ r : ℝ, b (2 * |r|)) = ∫ t : ℝ in Ioi 0, b t := by
  let D : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (fun r => b (2 * r))
  have hscale : IntegrableOn (fun r : ℝ => b (2 * r)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff b 0 (by norm_num : (0 : ℝ) < 2)).2
    simpa only [mul_zero] using hb
  have hD : Integrable D volume := (integrable_indicator_iff measurableSet_Ioi).2 hscale
  have heq : (fun r : ℝ => D r + D (-r)) =ᵐ[volume]
      (fun r : ℝ => b (2 * |r|)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · simp [D, Set.mem_Ioi, hneg.not_gt, neg_pos.mpr hneg, abs_of_neg hneg]
    · have hn : ¬0 < -r := by linarith
      simp [D, Set.mem_Ioi, hpos, hn, abs_of_pos hpos]
  refine ⟨(hD.add hD.comp_neg).congr heq, ?_⟩
  calc
    _ = ∫ r : ℝ, D r + D (-r) := (integral_congr_ae heq).symm
    _ = (∫ r : ℝ, D r) + ∫ r : ℝ, D (-r) := integral_add hD hD.comp_neg
    _ = (∫ r : ℝ, D r) + ∫ r : ℝ, D r := by rw [integral_neg_eq_self]
    _ = (∫ r : ℝ in Ioi 0, b (2 * r)) +
        ∫ r : ℝ in Ioi 0, b (2 * r) := by
      rw [show (∫ r : ℝ, D r) = ∫ r : ℝ in Ioi 0, b (2 * r) from
        integral_indicator measurableSet_Ioi]
    _ = _ := by
      rw [integral_comp_mul_left_Ioi b 0 (by norm_num : (0 : ℝ) < 2), mul_zero]
      norm_num [Complex.real_smul, smul_eq_mul] <;> ring

private theorem meanZeroActualMean_formula (F : ℝ → ℂ)
    (hu : IntegrableOn (actualGammaProfile F) (Ioi (0 : ℝ))) :
    meanZeroActualMean F =
      -(1 / 5 : ℂ) * (∫ t : ℝ in Ioi 0, actualGammaProfile F t) +
        (6 / 5 : ℂ) * rightExponentialTail (5 / 4) (actualGammaProfile F) 0 := by
  obtain ⟨hr, hmass⟩ := right_exponential_tail_l1_integrable_and_mass
    (by norm_num : (0 : ℝ) < 5 / 4) (actualGammaProfile F) hu
  have hb : IntegrableOn (actualSuzukiBProfile F) (Ioi (0 : ℝ)) :=
    hu.sub (hr.const_mul (3 / 2 : ℂ))
  have heven := (meanZeroEvenDouble_l1_mass (actualSuzukiBProfile F) hb).2
  change (∫ r : ℝ, actualSuzukiBProfile F (2 * |r|)) = _
  rw [heven]
  simp only [actualSuzukiBProfile]
  rw [integral_sub hu (hr.const_mul _), integral_const_mul, hmass]
  norm_num
  ring

private theorem meanZeroSeparatedFeature_mean_linear {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (a : ℂ) :
    meanZeroActualMean (meanZeroSeparatedFeature κ a) =
      meanZeroActualMean (finitePhysicalFeature 0 κ) -
        a * meanZeroActualMean (finitePhysicalFeature 0 (κ / 4)) := by
  have hlarge := finitePhysical_actualProfile_eq 0
    hκ hκ1
  have hsmall := finitePhysical_actualProfile_eq 0
    (by positivity : (0 : ℝ) < κ / 4) (by linarith : κ / 4 ≤ 1)
  have hilarge := meanZeroFiniteProfile_integrable hκ
  have hismall := meanZeroFiniteProfile_integrable (by positivity : (0 : ℝ) < κ / 4)
  have hularge : IntegrableOn (actualGammaProfile (finitePhysicalFeature 0 κ))
      (Ioi (0 : ℝ)) := by rw [hlarge]; exact hilarge.integrableOn
  have husmall : IntegrableOn (actualGammaProfile (finitePhysicalFeature 0 (κ / 4)))
      (Ioi (0 : ℝ)) := by rw [hsmall]; exact hismall.integrableOn
  have hucomb : IntegrableOn (actualGammaProfile (meanZeroSeparatedFeature κ a))
      (Ioi (0 : ℝ)) := by
    rw [meanZeroSeparatedFeature_actualProfile_eq hκ hκ1 a]
    exact (hilarge.sub (hismall.const_mul a)).integrableOn
  have hmass : (∫ t : ℝ in Ioi 0, actualGammaProfile (meanZeroSeparatedFeature κ a) t) =
      (∫ t : ℝ in Ioi 0, actualGammaProfile (finitePhysicalFeature 0 κ) t) -
        a * ∫ t : ℝ in Ioi 0, actualGammaProfile (finitePhysicalFeature 0 (κ / 4)) t := by
    rw [meanZeroSeparatedFeature_actualProfile_eq hκ hκ1 a, hlarge, hsmall,
      integral_sub hilarge.integrableOn (hismall.integrableOn.const_mul a), integral_const_mul]
  have hiweight (κ : ℝ) (hκ : 0 < κ) :
      IntegrableOn (fun t : ℝ => (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) *
        finiteCompressedProfile 0 κ t) (Ioi (0 : ℝ)) := by
    exact (meanZeroFiniteProfile_continuous_mul_integrable hκ _ (by fun_prop)).integrableOn
  have hlap : rightExponentialTail (5 / 4) (actualGammaProfile (meanZeroSeparatedFeature κ a)) 0 =
      rightExponentialTail (5 / 4) (actualGammaProfile (finitePhysicalFeature 0 κ)) 0 -
        a * rightExponentialTail (5 / 4) (actualGammaProfile (finitePhysicalFeature 0 (κ / 4))) 0 := by
    simp only [rightExponentialTail, zero_add,
      meanZeroSeparatedFeature_actualProfile_eq hκ hκ1 a, hlarge, hsmall]
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * finiteCompressedProfile 0 κ t -
            a * ((Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * finiteCompressedProfile 0 (κ / 4) t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by ring
      _ = _ := by
        rw [integral_sub (hiweight κ hκ)
          ((hiweight (κ / 4) (by positivity)).const_mul a), integral_const_mul]
  rw [meanZeroActualMean_formula _ hucomb,
    meanZeroActualMean_formula _ hularge, meanZeroActualMean_formula _ husmall, hmass, hlap]
  ring

private theorem meanZeroFiniteFeature_excess_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖finitePhysicalFeature 0 κ x‖ ^ 2 := by
  let d : ℝ → ℝ := fun x =>
    ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖finitePhysicalFeature 0 κ x‖ ^ 2
  have hd : Continuous d :=
    (((continuous_id.div_const Real.pi).pow 6).sub continuous_const).mul
      ((finitePhysical_continuous 0 hκ).norm.pow 2)
  have hi : Integrable d volume := hd.integrable_of_hasCompactSupport
    (finitePhysical_density_compact 0 hκ _)
  have hnn (x : ℝ) : 0 ≤ d x := by
    by_cases hx : x ≤ Real.pi
    · simp only [d, finitePhysical_zero_le_pi 0 hκ hx, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · have hr : 1 ≤ x / Real.pi :=
        (le_div_iff₀ Real.pi_pos).2 (by linarith [le_of_not_ge hx])
      exact mul_nonneg (sub_nonneg.2 (one_le_pow₀ hr)) (sq_nonneg _)
  have hwhole : (∫ x : ℝ in Ioi Real.pi, d x) = ∫ x : ℝ, d x := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ioi Real.pi
    · simp only [Set.indicator_of_mem hx]
    · simp only [d, finitePhysical_zero_le_pi 0 hκ (le_of_not_gt hx),
        norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        Set.indicator_of_notMem hx]
  change 0 < ∫ x : ℝ in Ioi Real.pi, d x
  rw [hwhole]
  apply integral_pos_of_integrable_nonneg_nonzero hd hi hnn
    (x := Real.pi * Real.exp (κ / 2))
  have hr : 1 < (Real.pi * Real.exp (κ / 2)) / Real.pi := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hw : 0 < ((Real.pi * Real.exp (κ / 2)) / Real.pi) ^ (6 : ℕ) - 1 :=
    sub_pos.2 (one_lt_pow₀ hr (by decide : (6 : ℕ) ≠ 0))
  exact ne_of_gt (mul_pos hw (pow_pos
    (norm_pos_iff.mpr (finitePhysical_center_ne 0 hκ)) 2))

private theorem meanZeroScaled_construct {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (∀ x : ℝ, Real.pi ≤ x →
        HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) ∧
      Function.support F ⊆ Icc Real.pi (Real.pi * Real.exp (3 * κ / 4)) := by
  have hsmall : (0 : ℝ) < κ / 4 := by positivity
  have hsmall1 : κ / 4 ≤ 1 := by linarith
  by_cases hμ : meanZeroActualMean (finitePhysicalFeature 0 (κ / 4)) = 0
  · refine ⟨finitePhysicalFeature 0 (κ / 4), finitePhysical_h6 0 hsmall,
      hμ, ?_, ?_, meanZeroFiniteFeature_excess_pos hsmall, ?_⟩
    · exact fun c => finitePhysical_in_all_shift_domains 0 hsmall hsmall1 c
    · exact fun x hx => finitePhysical_fullHasSum 0 hsmall hsmall1 hx
    · intro x hx
      have hs := finitePhysical_support 0 hsmall hx
      refine ⟨hs.1, hs.2.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      exact Real.exp_le_exp.mpr (by linarith [hκ])
  · let a : ℂ := meanZeroActualMean (finitePhysicalFeature 0 κ) /
        meanZeroActualMean (finitePhysicalFeature 0 (κ / 4))
    refine ⟨meanZeroSeparatedFeature κ a, meanZeroSeparatedFeature_h6 hκ a,
      ?_, meanZeroSeparatedFeature_in_all_shift_domains hκ hκ1 a, ?_,
      meanZeroSeparatedFeature_excess_pos hκ a,
      meanZeroSeparatedFeature_support hκ a⟩
    · change meanZeroActualMean (meanZeroSeparatedFeature κ a) = 0
      rw [meanZeroSeparatedFeature_mean_linear hκ hκ1 a]
      dsimp only [a]
      rw [div_mul_cancel₀ _ hμ, sub_self]
    · exact fun x hx => meanZeroSeparatedFeature_fullHasSum hκ hκ1 a hx

private theorem physical_sixth_cap_of_support (F : ℝ → ℂ)
    (hF : originalPhysicalH6 F) (κ : ℝ)
    (hs : Function.support F ⊆ Icc Real.pi (Real.pi * Real.exp (3 * κ / 4))) :
    (∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) ≤
      Real.exp (9 * κ / 2) * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) := by
  have hm := hF.1.integrable_norm_pow (p := 2) (by norm_num)
  rw [← integral_const_mul]
  apply integral_mono hF.2 (hm.const_mul _)
  intro x
  by_cases hz : F x = 0
  · simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  · have hx := hs hz
    have ha : 0 ≤ x / Real.pi :=
      div_nonneg (le_trans Real.pi_pos.le hx.1) Real.pi_pos.le
    have hb : x / Real.pi ≤ Real.exp (3 * κ / 4) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      simpa only [mul_comm] using hx.2
    have hc := pow_le_pow_left₀ ha hb 6
    have he : Real.exp (3 * κ / 4) ^ (6 : ℕ) = Real.exp (9 * κ / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he] at hc
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

/-- Actual even-B mean zero and every shifted Gamma domain do not raise the
infimum of the literal raw sixth-moment ratio above one. This concerns the
stated repository domain, not any additional original Suzuki admissibility. -/
theorem actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio
    (r : ℝ) (hr : 1 < r) :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∫ s : ℝ, actualSuzukiEvenBProfile F s) = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (∀ x : ℝ, Real.pi ≤ x →
        HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      (1 < (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) /
        (Real.pi ^ (6 : ℕ) * ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      ((∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) /
        (Real.pi ^ (6 : ℕ) * ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) < r) := by
  obtain ⟨κ, hκ, hκq, hκr⟩ := exists_cap_compression r hr
  obtain ⟨F, hF, hmean, hGamma, hsum, hpos, hs⟩ :=
    meanZeroScaled_construct hκ (by linarith : κ ≤ 1)
  let D : ℝ := ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2
  let M : ℝ := ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2
  have hm := hF.1.integrable_norm_pow (p := 2) (by norm_num)
  have hdiff : (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) = M - D := by
    simp_rw [sub_mul, one_mul]
    exact integral_sub hF.2 hm
  have hcap : M ≤ Real.exp (9 * κ / 2) * D := physical_sixth_cap_of_support F hF κ hs
  have hD : 0 < D := by
    have hDn : 0 ≤ D := integral_nonneg (fun x => sq_nonneg _)
    by_contra hn
    have hD0 : D = 0 := le_antisymm (le_of_not_gt hn) hDn
    rw [hD0, mul_zero] at hcap
    rw [hdiff, hD0, sub_zero] at hpos
    exact (not_lt_of_ge hcap) hpos
  have hlow : D < M := by rw [hdiff] at hpos; linarith
  have hupp : M < r * D :=
    hcap.trans_lt (mul_lt_mul_of_pos_right hκr hD)
  have hraw : (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) =
      Real.pi ^ (6 : ℕ) * M := by
    change (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) =
      Real.pi ^ (6 : ℕ) *
        (∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hratio : (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) /
      (Real.pi ^ (6 : ℕ) * D) = M / D := by
    rw [hraw]
    field_simp [Real.pi_ne_zero, ne_of_gt hD]
  refine ⟨F, hF, hmean, hGamma, hsum, hD, ?_, ?_⟩
  · rw [hratio]
    exact (lt_div_iff₀ hD).2 (by simpa only [one_mul] using hlow)
  · rw [hratio]
    exact (div_lt_iff₀ hD).2 hupp

/-- A nonzero original H6 input with actual even-B mean zero, all shifted Gamma
domains and positive original and fullTheta excess for the same source. -/
theorem actual_h6_mean_zero_positive_fullTheta_excess_all_gamma_domains :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (∀ x : ℝ, Real.pi ≤ x →
        HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2) := by
  obtain ⟨F, hF, hmean, hGamma, hsum, hpositive, _⟩ :=
    meanZeroScaled_construct (κ := 1) (by norm_num) (by norm_num)
  refine ⟨F, hF, hmean, hGamma, hsum, hpositive, ?_⟩
  have hexcess :
      (∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2) =
      (∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [show fullTheta F x = F x from (hsum x hx.le).tsum_eq]
  rw [hexcess]
  exact hpositive

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
