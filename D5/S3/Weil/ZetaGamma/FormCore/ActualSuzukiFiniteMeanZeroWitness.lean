/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteMeanZeroWitness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: One actual mean-zero H6 source with all shifted Gamma domains and positive original and fullTheta excess. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFinitePhysicalFeature
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy

open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology Function

private def meanZeroSeparatedFeature (a : ℂ) (x : ℝ) : ℂ :=
  finitePhysicalFeature 0 1 x - a * finitePhysicalFeature 0 (1 / 4) x

private theorem meanZeroSeparatedFeature_center_ne (a : ℂ) :
    meanZeroSeparatedFeature a (Real.pi * Real.exp (1 / 2)) ≠ 0 := by
  have hx : Real.pi ≤ Real.pi * Real.exp (1 / 2) := by
    have he : 1 ≤ Real.exp (1 / 2 : ℝ) :=
      Real.one_le_exp_iff.mpr (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hl : Real.log ((Real.pi * Real.exp (1 / 2)) / Real.pi) = (1 / 2 : ℝ) := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
  have hsmall : finitePhysicalFeature 0 (1 / 4) (Real.pi * Real.exp (1 / 2)) = 0 := by
    have hprof : finiteCompressedProfile 0 (1 / 4) (1 / 2) = 0 :=
      finiteCompressed_zero_off 0 (by norm_num)
        (by norm_num [Set.mem_Icc])
    simp only [finitePhysicalFeature, sourceOfProfile, if_pos hx, hl, hprof, mul_zero]
  simpa only [meanZeroSeparatedFeature, hsmall, mul_zero, sub_zero] using
    (finitePhysical_center_ne 0 (by norm_num : (0 : ℝ) < 1))

private theorem meanZeroSeparatedFeature_continuous (a : ℂ) :
    Continuous (meanZeroSeparatedFeature a) :=
  (finitePhysical_continuous 0 (by norm_num : (0 : ℝ) < 1)).sub
    (continuous_const.mul
      (finitePhysical_continuous 0 (by norm_num : (0 : ℝ) < 1 / 4)))

private theorem meanZeroSeparatedFeature_zero_le_pi (a : ℂ) {x : ℝ}
    (hx : x ≤ Real.pi) : meanZeroSeparatedFeature a x = 0 := by
  simp only [meanZeroSeparatedFeature,
    finitePhysical_zero_le_pi 0 (by norm_num : (0 : ℝ) < 1) hx,
    finitePhysical_zero_le_pi 0 (by norm_num : (0 : ℝ) < 1 / 4) hx,
    mul_zero, sub_self]

private theorem meanZeroSeparatedFeature_support (a : ℂ) :
    Function.support (meanZeroSeparatedFeature a) ⊆
      Icc Real.pi (Real.pi * Real.exp (3 / 4)) := by
  intro x hx
  by_contra hn
  have hlarge : finitePhysicalFeature 0 1 x = 0 := by
    by_contra h
    exact hn (by simpa only [mul_one] using
      finitePhysical_support 0 (by norm_num : (0 : ℝ) < 1) h)
  have hsmall : finitePhysicalFeature 0 (1 / 4) x = 0 := by
    by_contra h
    have hs := finitePhysical_support 0 (by norm_num : (0 : ℝ) < 1 / 4) h
    apply hn
    refine ⟨hs.1, hs.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact Real.exp_le_exp.mpr (by norm_num)
  exact hx (by simp only [meanZeroSeparatedFeature, hlarge, hsmall, mul_zero, sub_self])

private theorem meanZeroSeparatedFeature_compact (a : ℂ) :
    HasCompactSupport (meanZeroSeparatedFeature a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (meanZeroSeparatedFeature_support a)

private theorem meanZeroSeparatedFeature_density_compact (a : ℂ) (w : ℝ → ℝ) :
    HasCompactSupport (fun x : ℝ => w x * ‖meanZeroSeparatedFeature a x‖ ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.pi) (b := Real.pi * Real.exp (3 / 4)))
  intro x hx
  by_contra hn
  have hz : meanZeroSeparatedFeature a x = 0 := by
    by_contra h
    exact hn (meanZeroSeparatedFeature_support a h)
  exact hx (by simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero])

private theorem meanZeroSeparatedFeature_h6 (a : ℂ) :
    originalPhysicalH6 (meanZeroSeparatedFeature a) := by
  refine ⟨?_, ?_⟩
  · exact ((meanZeroSeparatedFeature_continuous a).memLp_of_hasCompactSupport
      (meanZeroSeparatedFeature_compact a)).mono_measure Measure.restrict_le_self
  · have hc : Continuous (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
        ‖meanZeroSeparatedFeature a x‖ ^ 2) :=
      ((continuous_id.div_const Real.pi).pow 6).mul
        ((meanZeroSeparatedFeature_continuous a).norm.pow 2)
    exact (hc.integrable_of_hasCompactSupport
      (meanZeroSeparatedFeature_density_compact a _)).integrableOn

private theorem meanZeroSeparatedFeature_excess_pos (a : ℂ) :
    0 < ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖meanZeroSeparatedFeature a x‖ ^ 2 := by
  let d : ℝ → ℝ := fun x =>
    ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖meanZeroSeparatedFeature a x‖ ^ 2
  have hd : Continuous d :=
    (((continuous_id.div_const Real.pi).pow 6).sub continuous_const).mul
      ((meanZeroSeparatedFeature_continuous a).norm.pow 2)
  have hi : Integrable d volume := hd.integrable_of_hasCompactSupport
    (meanZeroSeparatedFeature_density_compact a _)
  have hnn (x : ℝ) : 0 ≤ d x := by
    by_cases hx : x ≤ Real.pi
    · simp only [d, meanZeroSeparatedFeature_zero_le_pi a hx, norm_zero,
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
    · simp only [d, meanZeroSeparatedFeature_zero_le_pi a (le_of_not_gt hx),
        norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        Set.indicator_of_notMem hx]
  change 0 < ∫ x : ℝ in Ioi Real.pi, d x
  rw [hwhole]
  apply integral_pos_of_integrable_nonneg_nonzero hd hi hnn
    (x := Real.pi * Real.exp (1 / 2))
  have hratio : 1 < (Real.pi * Real.exp (1 / 2)) / Real.pi := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  let y : ℝ := (Real.pi * Real.exp (1 / 2)) / Real.pi
  have hy : 1 < y := hratio
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  have hweight : 0 < y ^ (6 : ℕ) - 1 := by
    rw [show y ^ (6 : ℕ) - 1 =
      (y - 1) * (y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1) by ring]
    exact mul_pos (sub_pos.2 hy) (by positivity)
  apply ne_of_gt
  exact mul_pos hweight (pow_pos
    (norm_pos_iff.mpr (meanZeroSeparatedFeature_center_ne a)) 2)

private theorem meanZeroSeparatedFeature_fullHasSum (a : ℂ) {x : ℝ}
    (hx : Real.pi ≤ x) :
    HasSum (fun k : ℕ => physicalTerm (meanZeroSeparatedFeature a) k x)
      (meanZeroSeparatedFeature a x) := by
  have hlarge := finitePhysical_fullHasSum 0
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) hx
  have hsmall := finitePhysical_fullHasSum 0
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) hx
  convert hlarge.sub (hsmall.mul_left a) using 1
  · funext k
    simp only [meanZeroSeparatedFeature, physicalTerm]
    ring
  · rfl

private theorem meanZeroSeparatedFeature_actualProfile_eq (a : ℂ) :
    actualGammaProfile (meanZeroSeparatedFeature a) =
      fun t : ℝ => finiteCompressedProfile 0 1 t -
        a * finiteCompressedProfile 0 (1 / 4) t := by
  have hlarge := finitePhysical_actualProfile_eq 0
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
  have hsmall := finitePhysical_actualProfile_eq 0
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  funext t
  calc
    actualGammaProfile (meanZeroSeparatedFeature a) t =
        actualGammaProfile (finitePhysicalFeature 0 1) t -
          a * actualGammaProfile (finitePhysicalFeature 0 (1 / 4)) t := by
      by_cases ht : 0 ≤ t
      · have hx : Real.pi ≤ Real.pi * Real.exp t := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (Real.one_le_exp_iff.mpr ht) Real.pi_pos.le
        have hc := (meanZeroSeparatedFeature_fullHasSum a hx).tsum_eq
        have hl := (finitePhysical_fullHasSum 0
          (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) hx).tsum_eq
        have hs := (finitePhysical_fullHasSum 0
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) hx).tsum_eq
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

private theorem meanZeroSeparatedFeature_fourier (a : ℂ) (ξ : ℝ) :
    unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature a)) ξ =
      unitarySourceFourier (finiteCompressedProfile 0 1) ξ -
        a * unitarySourceFourier (finiteCompressedProfile 0 (1 / 4)) ξ := by
  rw [meanZeroSeparatedFeature_actualProfile_eq]
  simp only [unitarySourceFourier_eq_integral]
  rw [show (fun t : ℝ => sourcePhase ξ t *
        (finiteCompressedProfile 0 1 t - a * finiteCompressedProfile 0 (1 / 4) t)) =
      (fun t : ℝ => sourcePhase ξ t * finiteCompressedProfile 0 1 t -
        a * (sourcePhase ξ t * finiteCompressedProfile 0 (1 / 4) t)) from
      funext fun t => by ring,
    integral_sub
      (meanZeroFiniteProfile_phase_integrable (by norm_num : (0 : ℝ) < 1) ξ)
      ((meanZeroFiniteProfile_phase_integrable (by norm_num : (0 : ℝ) < 1 / 4) ξ).const_mul a),
    integral_const_mul]
  ring

private theorem meanZeroSeparatedFeature_in_all_shift_domains (a : ℂ) (c : ℝ) :
    originalGammaFormDomain c (meanZeroSeparatedFeature a) := by
  have hc (κ : ℝ) (hκ : 0 < κ) :
      Continuous (unitarySourceFourier (finiteCompressedProfile 0 κ)) := by
    unfold unitarySourceFourier
    exact continuous_const.mul
      ((Zeta23.EF.continuous_fourier_of_integrable
        (meanZeroFiniteProfile_integrable hκ)).comp (by fun_prop))
  have hfreq : Continuous
      (unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature a))) := by
    convert (hc 1 (by norm_num)).sub
      (continuous_const.mul (hc (1 / 4) (by norm_num))) using 1
    funext ξ
    exact meanZeroSeparatedFeature_fourier a ξ
  have hlarge := finiteCompressed_all_shift_integrable 0
    (by norm_num : (0 : ℝ) < 1) |c|
  have hsmall := finiteCompressed_all_shift_integrable 0
    (by norm_num : (0 : ℝ) < 1 / 4) |c|
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
      ‖unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature a)) ξ‖ ^ 2 ≤
        2 * ‖unitarySourceFourier (finiteCompressedProfile 0 1) ξ‖ ^ 2 +
        2 * ‖a‖ ^ 2 * ‖unitarySourceFourier (finiteCompressedProfile 0 (1 / 4)) ξ‖ ^ 2 := by
    rw [meanZeroSeparatedFeature_fourier]
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_le (unitarySourceFourier (finiteCompressedProfile 0 1) ξ)
        (a * unitarySourceFourier (finiteCompressedProfile 0 (1 / 4)) ξ)) 2
    rw [norm_mul] at h
    nlinarith only [h, sq_nonneg
      (‖unitarySourceFourier (finiteCompressedProfile 0 1) ξ‖ -
        ‖a‖ * ‖unitarySourceFourier (finiteCompressedProfile 0 (1 / 4)) ξ‖)]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg
      ‖unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature a)) ξ‖)]
  calc
    _ ≤ (Symbol.gammaWeight ξ + |c|) *
        ‖unitarySourceFourier (actualGammaProfile (meanZeroSeparatedFeature a)) ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hg (sq_nonneg _)
    _ ≤ (Symbol.gammaWeight ξ + |c|) *
        (2 * ‖unitarySourceFourier (finiteCompressedProfile 0 1) ξ‖ ^ 2 +
          2 * ‖a‖ ^ 2 * ‖unitarySourceFourier (finiteCompressedProfile 0 (1 / 4)) ξ‖ ^ 2) :=
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

private theorem meanZeroSeparatedFeature_mean_linear (a : ℂ) :
    meanZeroActualMean (meanZeroSeparatedFeature a) =
      meanZeroActualMean (finitePhysicalFeature 0 1) -
        a * meanZeroActualMean (finitePhysicalFeature 0 (1 / 4)) := by
  have hlarge := finitePhysical_actualProfile_eq 0
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
  have hsmall := finitePhysical_actualProfile_eq 0
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hilarge := meanZeroFiniteProfile_integrable (by norm_num : (0 : ℝ) < 1)
  have hismall := meanZeroFiniteProfile_integrable (by norm_num : (0 : ℝ) < 1 / 4)
  have hularge : IntegrableOn (actualGammaProfile (finitePhysicalFeature 0 1))
      (Ioi (0 : ℝ)) := by rw [hlarge]; exact hilarge.integrableOn
  have husmall : IntegrableOn (actualGammaProfile (finitePhysicalFeature 0 (1 / 4)))
      (Ioi (0 : ℝ)) := by rw [hsmall]; exact hismall.integrableOn
  have hucomb : IntegrableOn (actualGammaProfile (meanZeroSeparatedFeature a))
      (Ioi (0 : ℝ)) := by
    rw [meanZeroSeparatedFeature_actualProfile_eq]
    exact (hilarge.sub (hismall.const_mul a)).integrableOn
  have hmass : (∫ t : ℝ in Ioi 0, actualGammaProfile (meanZeroSeparatedFeature a) t) =
      (∫ t : ℝ in Ioi 0, actualGammaProfile (finitePhysicalFeature 0 1) t) -
        a * ∫ t : ℝ in Ioi 0, actualGammaProfile (finitePhysicalFeature 0 (1 / 4)) t := by
    rw [meanZeroSeparatedFeature_actualProfile_eq, hlarge, hsmall,
      integral_sub hilarge.integrableOn (hismall.integrableOn.const_mul a), integral_const_mul]
  have hiweight (κ : ℝ) (hκ : 0 < κ) :
      IntegrableOn (fun t : ℝ => (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) *
        finiteCompressedProfile 0 κ t) (Ioi (0 : ℝ)) := by
    exact (meanZeroFiniteProfile_continuous_mul_integrable hκ _ (by fun_prop)).integrableOn
  have hlap : rightExponentialTail (5 / 4) (actualGammaProfile (meanZeroSeparatedFeature a)) 0 =
      rightExponentialTail (5 / 4) (actualGammaProfile (finitePhysicalFeature 0 1)) 0 -
        a * rightExponentialTail (5 / 4) (actualGammaProfile (finitePhysicalFeature 0 (1 / 4))) 0 := by
    simp only [rightExponentialTail, zero_add,
      meanZeroSeparatedFeature_actualProfile_eq, hlarge, hsmall]
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * finiteCompressedProfile 0 1 t -
            a * ((Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * finiteCompressedProfile 0 (1 / 4) t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by ring
      _ = _ := by
        rw [integral_sub (hiweight 1 (by norm_num))
          ((hiweight (1 / 4) (by norm_num)).const_mul a), integral_const_mul]
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
  have hconstruct : ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (∀ x : ℝ, Real.pi ≤ x →
        HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) := by
    by_cases hμ : meanZeroActualMean (finitePhysicalFeature 0 (1 / 4)) = 0
    · refine ⟨finitePhysicalFeature 0 (1 / 4),
        finitePhysical_h6 0 (by norm_num : (0 : ℝ) < 1 / 4), ?_, ?_, ?_,
        meanZeroFiniteFeature_excess_pos (by norm_num : (0 : ℝ) < 1 / 4)⟩
      · exact hμ
      · intro c
        exact finitePhysical_in_all_shift_domains 0
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) c
      · intro x hx
        exact finitePhysical_fullHasSum 0
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) hx
    · let a : ℂ := meanZeroActualMean (finitePhysicalFeature 0 1) /
        meanZeroActualMean (finitePhysicalFeature 0 (1 / 4))
      refine ⟨meanZeroSeparatedFeature a, meanZeroSeparatedFeature_h6 a,
        ?_, meanZeroSeparatedFeature_in_all_shift_domains a, ?_,
        meanZeroSeparatedFeature_excess_pos a⟩
      · change meanZeroActualMean (meanZeroSeparatedFeature a) = 0
        rw [meanZeroSeparatedFeature_mean_linear]
        dsimp only [a]
        rw [div_mul_cancel₀ _ hμ, sub_self]
      · intro x hx
        exact meanZeroSeparatedFeature_fullHasSum a hx
  obtain ⟨F, hF, hmean, hGamma, hsum, hpositive⟩ := hconstruct
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
