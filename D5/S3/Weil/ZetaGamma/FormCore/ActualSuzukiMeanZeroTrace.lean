/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-original-source-moment-domains)
   anchors: []
   utility: none
   digest: Actual mean-zero two-moment bounds and original-H6 Gamma profile L1/L2 domains. -/

/- The original H6 source determines its complete theta transform and actual
Gamma profile. Vanishing of the actual even-B mean bounds two Laplace moments
by the fullTheta sixth-moment excess. H6 also gives profile L1 and L2 on the
positive half-line. The endpoint trace is retained; Gamma-weighted Fourier
form-domain membership is a separate condition. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open scoped Topology ENNReal

/-- W338's actual B image of its already defined complete theta profile. -/
def actualSuzukiBProfile (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  actualGammaProfile F t -
    (3 / 2 : ℂ) * rightExponentialTail (5 / 4) (actualGammaProfile F) t

/-- W338's actual even arithmetic profile, with its exact factor two. -/
def actualSuzukiEvenBProfile (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  actualSuzukiBProfile F (2 * |r|)

theorem physical_h6_weighted_l1
    (U : ℝ → ℂ) (hU : originalPhysicalH6 U)
    (β : ℝ) (hβ : β < 5 / 2) :
    IntegrableOn (fun x : ℝ => ((x ^ β : ℝ) : ℂ) * U x) (Ioi Real.pi) := by
  let f : ℝ → ℂ := fun x => ((x ^ (β - 3) : ℝ) : ℂ)
  let g : ℝ → ℂ := fun x => ((x ^ (3 : ℕ) : ℝ) : ℂ) * U x
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi Real.pi)) := by
    dsimp [f]
    fun_prop
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi Real.pi)) := by
    exact ((show Continuous (fun x : ℝ => ((x ^ (3 : ℕ) : ℝ) : ℂ)) by
      fun_prop).aestronglyMeasurable).mul hU.1.aestronglyMeasurable
  have hgsq : Integrable (fun x : ℝ => ‖g x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    convert hU.2.const_mul (Real.pi ^ (6 : ℕ)) using 1
    funext x
    dsimp [g]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hfsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    have hpow : IntegrableOn (fun x : ℝ => x ^ (2 * (β - 3))) (Ioi Real.pi) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) Real.pi_pos
    apply hpow.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Real.pi < x at hx
    have hx0 : 0 < x := Real.pi_pos.trans hx
    dsimp [f]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), ← Real.rpow_two,
      ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hf : MemLp f 2 (volume.restrict (Ioi Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm hfmeas).2 hfsq
  have hg : MemLp g 2 (volume.restrict (Ioi Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm hgmeas).2 hgsq
  apply (hf.integrable_mul hg).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change Real.pi < x at hx
  have hx0 : 0 < x := Real.pi_pos.trans hx
  change ((x ^ (β - 3) : ℝ) : ℂ) * (((x ^ (3 : ℕ) : ℝ) : ℂ) * U x) =
    ((x ^ β : ℝ) : ℂ) * U x
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_natCast x 3,
    ← Real.rpow_add hx0]
  congr 2
  ring

private theorem physical_log_coordinate_l1_mass
    (U : ℝ → ℂ) (β : ℝ)
    (hi : IntegrableOn (fun x : ℝ => ((x ^ β : ℝ) : ℂ) * U x) (Ioi Real.pi)) :
    IntegrableOn
      (fun t : ℝ => (((Real.pi * Real.exp t) ^ (β + 1) : ℝ) : ℂ) *
        U (Real.pi * Real.exp t)) (Ioi (0 : ℝ)) ∧
    (∫ t : ℝ in Ioi 0, (((Real.pi * Real.exp t) ^ (β + 1) : ℝ) : ℂ) *
      U (Real.pi * Real.exp t)) =
      ∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * U x := by
  let h : ℝ → ℂ := fun x => ((x ^ β : ℝ) : ℂ) * U x
  let p : ℝ → ℂ := fun y => (Real.pi : ℂ) * h (Real.pi * y)
  have hc : IntegrableOn (fun y : ℝ => h (Real.pi * y)) (Ioi (1 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff h 1 Real.pi_pos).2
    simpa only [mul_one] using hi
  have hp : IntegrableOn p (Ioi (Real.exp (0 : ℝ))) := by
    simpa only [p, Real.exp_zero, IntegrableOn] using hc.const_mul (Real.pi : ℂ)
  have ht := (integrableOn_comp_exp_Ioi p 0).2 hp
  have he (t : ℝ) :
      Real.exp t • p (Real.exp t) =
        (((Real.pi * Real.exp t) ^ (β + 1) : ℝ) : ℂ) * U (Real.pi * Real.exp t) := by
    have hx : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    dsimp [p, h]
    rw [Real.rpow_add hx, Real.rpow_one]
    push_cast
    ring
  refine ⟨ht.congr (Eventually.of_forall he), ?_⟩
  calc
    _ = ∫ t : ℝ in Ioi 0, Real.exp t • p (Real.exp t) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => (he t).symm
    _ = ∫ y : ℝ in Ioi (1 : ℝ), p y := by
      simpa only [Real.exp_zero] using integral_comp_exp_Ioi p 0
    _ = (Real.pi : ℂ) * ((Real.pi⁻¹ : ℝ) •
        ∫ x : ℝ in Ioi Real.pi, h x) := by
      dsimp [p]
      rw [integral_const_mul]
      congr 1
      simpa only [mul_one, Complex.real_smul] using integral_comp_mul_left_Ioi h 1 Real.pi_pos
    _ = _ := by
      simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

theorem actual_profile_l1_and_physical_moments
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    IntegrableOn (actualGammaProfile F) (Ioi (0 : ℝ)) ∧
    (∫ t : ℝ in Ioi 0, actualGammaProfile F t) =
      (∫ x : ℝ in Ioi Real.pi, ((x ^ (5 / 4 : ℝ) : ℝ) : ℂ) * fullTheta F x) ∧
    rightExponentialTail (5 / 4) (actualGammaProfile F) 0 =
      ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        ∫ x : ℝ in Ioi Real.pi, fullTheta F x := by
  have hU := (actual_h6_fullTheta_excess_bound F hF).1
  have h5 := physical_log_coordinate_l1_mass (fullTheta F) (5 / 4)
    (physical_h6_weighted_l1 _ hU (5 / 4) (by norm_num))
  have h0 := physical_log_coordinate_l1_mass (fullTheta F) 0
    (by simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using
      physical_h6_weighted_l1 _ hU 0 (by norm_num))
  have hpos : actualGammaProfile F =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => (((Real.pi * Real.exp t) ^ ((5 / 4 : ℝ) + 1) : ℝ) : ℂ) *
        fullTheta F (Real.pi * Real.exp t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    simp only [actualGammaProfile, if_pos ht.le]
    congr 2
    norm_num
  refine ⟨h5.1.congr hpos.symm, (integral_congr_ae hpos).trans h5.2, ?_⟩
  have hexp (t : ℝ) :
      Real.exp (-(5 / 4 : ℝ) * t) *
          (Real.pi * Real.exp t) ^ (5 / 4 : ℝ) =
        Real.pi ^ (5 / 4 : ℝ) := by
    calc
      _ = Real.pi ^ (5 / 4 : ℝ) *
          (Real.exp (-(5 / 4 : ℝ) * t) * Real.exp (t * (5 / 4 : ℝ))) := by
        rw [Real.mul_rpow Real.pi_pos.le (Real.exp_pos t).le,
          Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
        ring
      _ = _ := by
        rw [← Real.exp_add, show -(5 / 4 : ℝ) * t + t * (5 / 4 : ℝ) = 0 by ring,
          Real.exp_zero, mul_one]
  calc
    rightExponentialTail (5 / 4) (actualGammaProfile F) 0 =
        ∫ t : ℝ in Ioi 0, ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
          ((((Real.pi * Real.exp t) ^ ((0 : ℝ) + 1) : ℝ) : ℂ) *
            fullTheta F (Real.pi * Real.exp t)) := by
      unfold rightExponentialTail
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      simp only [zero_add, actualGammaProfile, if_pos ht.le]
      have hx : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
      rw [show (9 / 4 : ℝ) = (5 / 4 : ℝ) + 1 by ring,
        Real.rpow_add hx, Real.rpow_one]
      norm_num only [zero_add, Real.rpow_one]
      push_cast
      have hs := congrArg (fun r : ℝ => (r : ℂ)) (hexp t)
      push_cast at hs
      linear_combination (Real.pi : ℂ) * Complex.exp (t : ℂ) *
        fullTheta F (Real.pi * Real.exp t) * hs
    _ = ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        ∫ t : ℝ in Ioi 0,
          (((Real.pi * Real.exp t) ^ ((0 : ℝ) + 1) : ℝ) : ℂ) *
            fullTheta F (Real.pi * Real.exp t) := integral_const_mul _ _
    _ = _ := by
      rw [h0.2]
      simp only [Real.rpow_zero, Complex.ofReal_one, one_mul]

theorem even_double_l1_mass
    (b : ℝ → ℂ) (hb : IntegrableOn b (Ioi (0 : ℝ))) :
    Integrable (fun r : ℝ => b (2 * |r|)) volume ∧
    (∫ r : ℝ, b (2 * |r|)) = ∫ t : ℝ in Ioi 0, b t := by
  let D : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (fun r => b (2 * r))
  have hscale : IntegrableOn (fun r : ℝ => b (2 * r)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff b 0 (by norm_num : (0 : ℝ) < 2)).2
    simpa only [mul_zero] using hb
  have hD : Integrable D volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hscale
  have heq : (fun r : ℝ => D r + D (-r)) =ᵐ[volume]
      (fun r : ℝ => b (2 * |r|)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · simp [D, Set.mem_Ioi, hneg.not_gt, neg_pos.mpr hneg, abs_of_neg hneg]
    · have hn : ¬ 0 < -r := by linarith
      simp [D, Set.mem_Ioi, hpos, hn, abs_of_pos hpos]
  have hi := (hD.add hD.comp_neg).congr heq
  refine ⟨hi, ?_⟩
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
      norm_num [Complex.real_smul, smul_eq_mul]
      ring

private theorem actual_mean_zero_trace_moment
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hmean : (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0) :
    (5 : ℂ) * rightExponentialTail (5 / 4) (actualGammaProfile F) 0 =
      ∫ x : ℝ in Ioi Real.pi,
        ((x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
          fullTheta F x := by
  obtain ⟨hiu, hU0, hA⟩ := actual_profile_l1_and_physical_moments F hF
  obtain ⟨hir, hrmass⟩ := right_exponential_tail_l1_integrable_and_mass
    (by norm_num : (0 : ℝ) < 5 / 4) (actualGammaProfile F) hiu
  have hib : IntegrableOn (actualSuzukiBProfile F) (Ioi (0 : ℝ)) :=
    hiu.sub (hir.const_mul (3 / 2 : ℂ))
  have hbmean : (∫ t : ℝ in Ioi 0, actualSuzukiBProfile F t) = 0 := by
    exact (even_double_l1_mass _ hib).2.symm.trans hmean
  have hm : (5 : ℂ) * rightExponentialTail (5 / 4) (actualGammaProfile F) 0 =
      (∫ t : ℝ in Ioi 0, actualGammaProfile F t) -
        rightExponentialTail (5 / 4) (actualGammaProfile F) 0 := by
    unfold actualSuzukiBProfile at hbmean
    rw [integral_sub hiu (hir.const_mul _), integral_const_mul, hrmass] at hbmean
    norm_num at hbmean
    linear_combination 5 * hbmean
  have hU := (actual_h6_fullTheta_excess_bound F hF).1
  have hi5 := physical_h6_weighted_l1 _ hU (5 / 4) (by norm_num)
  have hi0 : IntegrableOn (fullTheta F) (Ioi Real.pi) := by
    simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using
      physical_h6_weighted_l1 _ hU 0 (by norm_num)
  rw [hm, hU0, hA, ← integral_const_mul, ← integral_sub hi5 (hi0.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by push_cast; ring

private theorem actual_h6_physical_log_moment
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    IntegrableOn (fun x : ℝ => (Real.log (x / Real.pi) : ℂ) * fullTheta F x)
      (Ioi Real.pi) ∧
    IntegrableOn (fun t : ℝ => ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) *
      actualGammaProfile F t) (Ioi (0 : ℝ)) ∧
    (∫ t : ℝ in Ioi 0, ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) *
      actualGammaProfile F t) =
      ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        ∫ x : ℝ in Ioi Real.pi,
          (Real.log (x / Real.pi) : ℂ) * fullTheta F x := by
  have hT := (actual_h6_fullTheta_excess_bound F hF).1
  have hX : IntegrableOn (fun x : ℝ => (x : ℂ) * fullTheta F x)
      (Ioi Real.pi) := by
    simpa only [Real.rpow_one] using
      physical_h6_weighted_l1 (fullTheta F) hT 1 (by norm_num)
  have hLog : IntegrableOn
      (fun x : ℝ => (Real.log (x / Real.pi) : ℂ) * fullTheta F x)
      (Ioi Real.pi) := by
    apply (hX.norm.const_mul Real.pi⁻¹).mono'
      (((show Measurable (fun x : ℝ => (Real.log (x / Real.pi) : ℂ)) by
          fun_prop).aestronglyMeasurable).mul hT.1.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Real.pi < x at hx
    have hx0 : 0 < x := Real.pi_pos.trans hx
    have hxpi : 1 < x / Real.pi := (lt_div_iff₀ Real.pi_pos).2 (by simpa using hx)
    have hlog0 : 0 ≤ Real.log (x / Real.pi) := Real.log_nonneg hxpi.le
    have hlogle : Real.log (x / Real.pi) ≤ x / Real.pi := by
      linarith [Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hxpi)]
    calc
      _ = Real.log (x / Real.pi) * ‖fullTheta F x‖ := by
        simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlog0]
      _ ≤ (x / Real.pi) * ‖fullTheta F x‖ :=
        mul_le_mul_of_nonneg_right hlogle (norm_nonneg _)
      _ = _ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        ring
  let Tlog : ℝ → ℂ := fun x => (Real.log (x / Real.pi) : ℂ) * fullTheta F x
  have hChange := physical_log_coordinate_l1_mass Tlog 0
    (by simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using hLog)
  have hScale (t : ℝ) :
      Real.exp (-(5 / 4 : ℝ) * t) *
          (Real.pi * Real.exp t) ^ (5 / 4 : ℝ) =
        Real.pi ^ (5 / 4 : ℝ) := by
    calc
      _ = Real.pi ^ (5 / 4 : ℝ) *
          (Real.exp (-(5 / 4 : ℝ) * t) * Real.exp (t * (5 / 4 : ℝ))) := by
        rw [Real.mul_rpow Real.pi_pos.le (Real.exp_pos t).le,
          Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
        ring
      _ = _ := by
        rw [← Real.exp_add, show -(5 / 4 : ℝ) * t + t * (5 / 4 : ℝ) = 0 by ring,
          Real.exp_zero, mul_one]
  have hPoint : (fun t : ℝ => ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) *
      actualGammaProfile F t) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        ((((Real.pi * Real.exp t) ^ ((0 : ℝ) + 1) : ℝ) : ℂ) *
          Tlog (Real.pi * Real.exp t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hx : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    have hRatio : Real.pi * Real.exp t / Real.pi = Real.exp t := by
      field_simp [Real.pi_ne_zero]
    simp only [actualGammaProfile, if_pos ht.le, Tlog, hRatio, Real.log_exp,
      zero_add, Real.rpow_one]
    rw [show (9 / 4 : ℝ) = (5 / 4 : ℝ) + 1 by ring,
      Real.rpow_add hx, Real.rpow_one]
    push_cast
    have hs := congrArg (fun r : ℝ => (r : ℂ)) (hScale t)
    push_cast at hs
    linear_combination (t : ℂ) * (Real.pi : ℂ) * Complex.exp (t : ℂ) *
      fullTheta F (Real.pi * Real.exp t) * hs
  refine ⟨hLog, (hChange.1.const_mul _).congr hPoint.symm, ?_⟩
  calc
    _ = ∫ t : ℝ in Ioi 0, ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        ((((Real.pi * Real.exp t) ^ ((0 : ℝ) + 1) : ℝ) : ℂ) *
          Tlog (Real.pi * Real.exp t)) := integral_congr_ae hPoint
    _ = _ := by
      rw [integral_const_mul, hChange.2]
      simp only [Tlog, Real.rpow_zero, Complex.ofReal_one, one_mul]


/-- Original even-B mean zero controls both actual Gamma Laplace moments
in the SAME normalized fullTheta excess. Their actual L1 domains are paid. -/
theorem actual_h6_mean_zero_physical_moment_bounds
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hmean : (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0) :
    let L0 := ∫ t : ℝ in Ioi 0,
      (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t
    let Lt := ∫ t : ℝ in Ioi 0,
      ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) * actualGammaProfile F t
    let D := ∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2
    IntegrableOn (fun t : ℝ => (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) *
      actualGammaProfile F t) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun t : ℝ => ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) *
        actualGammaProfile F t) (Ioi (0 : ℝ)) ∧
      ‖L0‖ ^ 2 ≤ (3 / 1000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D ∧
      ‖Lt‖ ^ 2 ≤ (3 / 160 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D ∧
      ‖L0‖ * ‖Lt‖ ≤ (3 / 400 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D := by
  let L0 := ∫ t : ℝ in Ioi 0,
    (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t
  let Lt := ∫ t : ℝ in Ioi 0,
    ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) * actualGammaProfile F t
  let D := ∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2
  have hU := (actual_h6_fullTheta_excess_bound F hF).1
  obtain ⟨_, _, hTc, hLc⟩ :=
    D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma.actual_h6_weighted_physical_moments
      (fullTheta F) hU
  have hTrace : (5 : ℂ) * L0 =
      ∫ x : ℝ in Ioi Real.pi,
        ((x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * fullTheta F x := by
    simpa only [L0, rightExponentialTail, zero_add] using actual_mean_zero_trace_moment F hF hmean
  have hLog := actual_h6_physical_log_moment F hF
  have hZeroInt : IntegrableOn (fun t : ℝ => (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) *
      actualGammaProfile F t) (Ioi (0 : ℝ)) := by
    have hu := (actual_profile_l1_and_physical_moments F hF).1
    have hm : Continuous (fun t : ℝ => (Real.exp (-(5 / 4 : ℝ) * t) : ℂ)) := by fun_prop
    apply Integrable.mono hu (hm.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 1 * ‖actualGammaProfile F t‖ := mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.2 (by linarith : -(5 / 4 : ℝ) * t ≤ 0)) (norm_nonneg _)
      _ = _ := one_mul _
  have h0 : ‖L0‖ ^ 2 ≤ (3 / 1000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D := by
    have hNorm : ‖(5 : ℂ) * L0‖ ^ 2 = 25 * ‖L0‖ ^ 2 := by norm_num [norm_mul, mul_pow]
    rw [← hTrace, hNorm] at hTc
    calc
      _ = (25 * ‖L0‖ ^ 2) / 25 := by ring
      _ ≤ ((3 / 40 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D) / 25 :=
        div_le_div_of_nonneg_right hTc (by norm_num)
      _ = _ := by ring
  have h1 : ‖Lt‖ ^ 2 ≤ (3 / 160 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D := by
    have hPi : ‖((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ)‖ ^ 2 =
        Real.pi ^ (5 / 2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Real.rpow_two,
        ← Real.rpow_mul Real.pi_pos.le]
      norm_num
    have hPiScale : Real.pi ^ (5 / 2 : ℝ) * Real.pi = Real.pi ^ (7 / 2 : ℝ) := by
      calc
        _ = Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add Real.pi_pos]; norm_num
    calc
      _ = Real.pi ^ (5 / 2 : ℝ) *
          ‖∫ x : ℝ in Ioi Real.pi, (Real.log (x / Real.pi) : ℂ) * fullTheta F x‖ ^ 2 := by
        change ‖(∫ t : ℝ in Ioi 0,
          ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) * actualGammaProfile F t)‖ ^ 2 = _
        rw [hLog.2.2, norm_mul, mul_pow, hPi]
      _ ≤ Real.pi ^ (5 / 2 : ℝ) * ((3 / 160 : ℝ) * Real.pi * D) :=
        mul_le_mul_of_nonneg_left hLc (by positivity)
      _ = (3 / 160 : ℝ) * (Real.pi ^ (5 / 2 : ℝ) * Real.pi) * D := by ring
      _ = _ := by rw [hPiScale]
  have hD : 0 ≤ D := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Real.pi < x at hx
    have hxpi : 1 ≤ x / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by linarith [hx])
    exact mul_nonneg (sub_nonneg.2 (one_le_pow₀ hxpi)) (sq_nonneg _)
  have hProdSq : (‖L0‖ * ‖Lt‖) ^ 2 ≤
      ((3 / 400 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D) ^ 2 := by
    have hh := mul_le_mul h0 h1 (sq_nonneg ‖Lt‖)
      (by positivity : (0 : ℝ) ≤ (3 / 1000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D)
    convert hh using 1 <;> ring
  refine ⟨hZeroInt, hLog.2.1, h0, h1, ?_⟩
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg L0) (norm_nonneg Lt)) (by positivity)).1 hProdSq

/- The physical coordinate identities give profile L1 and L2 without an
additional Gamma-weighted Fourier form-domain hypothesis. -/

/-- The SAME original H6 source supplies genuine L1 and L2 domains for
its actual complete-theta Gamma profile on the positive half-line. -/
theorem actual_h6_gamma_profile_l1_l2
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    IntegrableOn (actualGammaProfile F) (Ioi (0 : ℝ)) ∧
      MemLp (actualGammaProfile F) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hu₁ := (actual_profile_l1_and_physical_moments F hF).1
  have hU := (actual_h6_fullTheta_excess_bound F hF).1
  let h : ℝ → ℝ := fun x => x ^ (7 / 2 : ℝ) * ‖fullTheta F x‖ ^ 2
  have hm : AEStronglyMeasurable h (volume.restrict (Ioi Real.pi)) := by
    exact (show Continuous (fun x : ℝ => x ^ (7 / 2 : ℝ)) by
      fun_prop).aestronglyMeasurable.mul (hU.1.aestronglyMeasurable.norm.pow 2)
  have hh : IntegrableOn h (Ioi Real.pi) := by
    apply (hU.2.const_mul (Real.pi ^ (6 : ℕ))).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Real.pi < x at hx
    have hx0 : 0 < x := Real.pi_pos.trans hx
    have hx1 : 1 ≤ x := by linarith [Real.pi_gt_three]
    dsimp [h]
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (sq_nonneg _))]
    calc
      _ ≤ x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (by
            rw [← Real.rpow_natCast x 6]
            exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (sq_nonneg _)
      _ = _ := by field_simp [Real.pi_ne_zero]
  let p : ℝ → ℝ := fun y => Real.pi * h (Real.pi * y)
  have hc : IntegrableOn (fun y : ℝ => h (Real.pi * y)) (Ioi (1 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff h 1 Real.pi_pos).2
    simpa only [mul_one] using hh
  have hp : IntegrableOn p (Ioi (Real.exp (0 : ℝ))) := by
    simpa only [p, Real.exp_zero, IntegrableOn] using hc.const_mul Real.pi
  have ht := (integrableOn_comp_exp_Ioi p 0).2 hp
  have hsq : IntegrableOn (fun t : ℝ => ‖actualGammaProfile F t‖ ^ 2)
      (Ioi (0 : ℝ)) := by
    apply ht.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hx : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    have hpow : ((Real.pi * Real.exp t) ^ (9 / 4 : ℝ)) ^ (2 : ℕ) =
        (Real.pi * Real.exp t) * (Real.pi * Real.exp t) ^ (7 / 2 : ℝ) := by
      calc
        _ = (Real.pi * Real.exp t) ^ ((9 / 4 : ℝ) * 2) := by
          rw [Real.rpow_mul hx.le, Real.rpow_two]
        _ = (Real.pi * Real.exp t) ^ (1 + 7 / 2 : ℝ) := by norm_num
        _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
    simp only [actualGammaProfile, if_pos ht.le, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hpow]
    dsimp [p, h]
    ring
  exact ⟨hu₁, (memLp_two_iff_integrable_sq_norm hu₁.aestronglyMeasurable).2 hsq⟩


end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
