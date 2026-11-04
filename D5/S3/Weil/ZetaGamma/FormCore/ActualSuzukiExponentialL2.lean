/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-original-h6-weighted-domain)
   anchors: []
   utility: none
   digest: Original H6 controls the actual even-B critical exponential L2 domain and mass. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailGlobalL2
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate

/-! Critical exponential control for the actual profiles of one original H6 source. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

open MeasureTheory Set Filter
open scoped Topology

/-- Multiplying the actual future tail by an increasing exponential raises
its decay rate. This identity is for the actual Bochner integral. -/
theorem right_exponential_tail_exponential_conjugation
    (k a : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    (Real.exp (a * t) : ℂ) * rightExponentialTail k u t =
      rightExponentialTail (k + a)
        (fun x => (Real.exp (a * x) : ℂ) * u x) t := by
  rw [rightExponentialTail, rightExponentialTail, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    have he : Real.exp (a * t) * Real.exp (-k * s) =
        Real.exp (-(k + a) * s) * Real.exp (a * (t + s)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hec := congrArg (fun x : ℝ => (x : ℂ)) he
    simp only [Complex.ofReal_mul] at hec
    linear_combination u (t + s) * hec

end D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open scoped ENNReal Topology

open private actual_fullTheta_excess_memLp_norm thetaExcessMass thetaExcessDensity
  thetaModeCoefficient
  thetaExcess_mass_eq_sq_norm h6_thetaExcess_memLp from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess

/-- H6 gives the critical exponentially weighted Gamma-profile L2 domain.
The exponent 5/4 multiplies the amplitude; its squared weight is exp(5t/2).
This is a half-line input for B, not the full-line even B profile itself. -/
theorem actual_h6_gamma_profile_critical_exponential_l2_and_mass
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    MemLp (fun t : ℝ => (Real.exp ((5 / 4 : ℝ) * t) : ℂ) *
        actualGammaProfile F t) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t : ℝ in Ioi 0,
        ‖(Real.exp ((5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t‖ ^ 2) =
        Real.pi ^ (-(5 / 2 : ℝ)) *
          ∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by
  have hU := (actual_h6_fullTheta_excess_bound F hF).1
  let h : ℝ → ℝ := fun x => x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2
  have hh : IntegrableOn h (Ioi Real.pi) := by
    change Integrable h (volume.restrict (Ioi Real.pi))
    have heq : h = fun x => Real.pi ^ (6 : ℕ) *
        ((x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2) := by
      funext x
      dsimp [h]
      field_simp [Real.pi_ne_zero]
    rw [heq]
    exact hU.2.const_mul (Real.pi ^ (6 : ℕ))
  let p : ℝ → ℝ := fun y => Real.pi * h (Real.pi * y)
  have hc : IntegrableOn (fun y : ℝ => h (Real.pi * y)) (Ioi (1 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff h 1 Real.pi_pos).2
    simpa only [mul_one] using hh
  have hp : IntegrableOn p (Ioi (Real.exp (0 : ℝ))) := by
    simpa only [p, Real.exp_zero, IntegrableOn] using hc.const_mul Real.pi
  have ht := (integrableOn_comp_exp_Ioi p 0).2 hp
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (Real.exp ((5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (show Continuous (fun t : ℝ => (Real.exp ((5 / 4 : ℝ) * t) : ℂ)) by
      fun_prop).aestronglyMeasurable.mul
        (actual_h6_gamma_profile_l1_l2 F hF).2.aestronglyMeasurable
  have hpoint :
      (fun t : ℝ => Real.pi ^ (-(5 / 2 : ℝ)) * (Real.exp t • p (Real.exp t)))
        =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => ‖(Real.exp ((5 / 4 : ℝ) * t) : ℂ) *
        actualGammaProfile F t‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hx : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    have he : Real.exp ((5 / 4 : ℝ) * t) ^ (2 : ℕ) =
        Real.exp ((5 / 2 : ℝ) * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hcoeff : Real.exp ((5 / 2 : ℝ) * t) *
        ((Real.pi * Real.exp t) ^ (9 / 4 : ℝ)) ^ (2 : ℕ) =
          Real.pi ^ (-(5 / 2 : ℝ)) *
            (Real.pi * Real.exp t) * (Real.pi * Real.exp t) ^ (6 : ℕ) := by
      calc
        _ = Real.exp ((5 / 2 : ℝ) * t +
            (Real.log Real.pi + t) * (9 / 4 : ℝ) * 2) := by
          rw [Real.rpow_def_of_pos hx, Real.log_mul Real.pi_ne_zero (Real.exp_ne_zero t),
            Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
        _ = Real.exp (Real.log Real.pi * (-(5 / 2 : ℝ)) +
            Real.log (Real.pi * Real.exp t) * (7 : ℝ)) := by
          rw [Real.log_mul Real.pi_ne_zero (Real.exp_ne_zero t), Real.log_exp]
          congr 1
          ring
        _ = Real.pi ^ (-(5 / 2 : ℝ)) * (Real.pi * Real.exp t) ^ (7 : ℕ) := by
          rw [Real.exp_add, ← Real.rpow_def_of_pos Real.pi_pos,
            ← Real.rpow_def_of_pos hx]
          norm_num
        _ = _ := by ring
    simp only [actualGammaProfile, if_pos ht.le, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, sq_abs]
    rw [he]
    dsimp [p, h]
    nlinarith [congrArg
      (fun z : ℝ => z * ‖fullTheta F (Real.pi * Real.exp t)‖ ^ 2) hcoeff]
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2
    ((ht.const_mul (Real.pi ^ (-(5 / 2 : ℝ)))).congr hpoint), ?_⟩
  have hpMass : (∫ t : ℝ in Ioi 0, Real.exp t • p (Real.exp t)) =
      ∫ x : ℝ in Ioi Real.pi, h x := by
    calc
      _ = ∫ y : ℝ in Ioi 1, p y := by
        simpa only [Real.exp_zero] using integral_comp_exp_Ioi p 0
      _ = Real.pi * ∫ y : ℝ in Ioi 1, h (Real.pi * y) := integral_const_mul _ _
      _ = _ := by
        rw [integral_comp_mul_left_Ioi h 1 Real.pi_pos]
        simp only [mul_one, smul_eq_mul]
        field_simp [Real.pi_ne_zero]
  rw [← integral_congr_ae hpoint, integral_const_mul, hpMass]

/-- The original H6 source supplies both the ordinary actual even-B L2
domain and its critical b=5/2 exponentially weighted L2 domain. Every
profile here is the actual profile of this same F. -/
theorem actual_h6_suzuki_even_b_l1_l2_critical_exponential
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    Integrable (actualSuzukiEvenBProfile F) volume ∧
      MemLp (actualSuzukiEvenBProfile F) 2 volume ∧
      MemLp (fun r : ℝ => (Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) *
        actualSuzukiEvenBProfile F r) 2 volume ∧
      (∫ r : ℝ,
        ‖(Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) * actualSuzukiEvenBProfile F r‖ ^ 2) ≤
        (68 / 25 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
          (∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) ^ 2 *
            (∫ x : ℝ in Ioi Real.pi,
              (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) := by
  have hfull1 := (actual_h6_suzuki_mean_charge_formula F hF).1
  have hu1 := (actual_h6_gamma_profile_l1_l2 F hF).1
  have hR1 := (RightExponentialTail.right_exponential_tail_l1_integrable_and_mass
    (by norm_num : (0 : ℝ) < 5 / 4) (actualGammaProfile F) hu1).1
  let v : ℝ → ℂ := fun t => (Real.exp ((5 / 4 : ℝ) * t) : ℂ) *
    actualGammaProfile F t
  obtain ⟨hv, hvMass⟩ := actual_h6_gamma_profile_critical_exponential_l2_and_mass F hF
  change MemLp v 2 (volume.restrict (Ioi (0 : ℝ))) at hv
  change (∫ t : ℝ in Ioi 0, ‖v t‖ ^ 2) = _ at hvMass
  have hconj (t : ℝ) :
      (Real.exp ((5 / 4 : ℝ) * t) : ℂ) *
        RightExponentialTail.rightExponentialTail (5 / 4) (actualGammaProfile F) t =
      RightExponentialTail.rightExponentialTail (5 / 2) v t := by
    simpa only [show (5 / 4 : ℝ) + 5 / 4 = 5 / 2 by norm_num, v] using
      RightExponentialTail.right_exponential_tail_exponential_conjugation
        (5 / 4) (5 / 4) (actualGammaProfile F) t
  have hRm : AEStronglyMeasurable
      (RightExponentialTail.rightExponentialTail (5 / 2) v)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply ((show Continuous (fun t : ℝ => (Real.exp ((5 / 4 : ℝ) * t) : ℂ)) by
      fun_prop).aestronglyMeasurable.mul hR1.aestronglyMeasurable).congr
    exact Eventually.of_forall hconj
  obtain ⟨hRv, hRvMass⟩ := RightExponentialTail.right_exponential_tail_memLp_two_and_mass_bound
    (by norm_num : (0 : ℝ) < 5 / 2) v hv hRm
  let wB : ℝ → ℂ := fun t => (Real.exp ((5 / 4 : ℝ) * t) : ℂ) *
    actualSuzukiBProfile F t
  have hwB_eq (t : ℝ) : wB t = v t - (3 / 2 : ℂ) *
      RightExponentialTail.rightExponentialTail (5 / 2) v t := by
    dsimp [wB, v, actualSuzukiBProfile]
    rw [← hconj t]
    ring
  have hwB : MemLp wB 2 (volume.restrict (Ioi (0 : ℝ))) := by
    apply (memLp_congr_ae ?_).1 (hv.sub (hRv.const_mul (3 / 2 : ℂ)))
    exact Eventually.of_forall fun t => (hwB_eq t).symm
  have hsquare := (memLp_two_iff_integrable_sq_norm hwB.aestronglyMeasurable).1 hwB
  have hsquareC : IntegrableOn (fun t : ℝ => ((‖wB t‖ ^ 2 : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
    change Integrable (fun t : ℝ => ((‖wB t‖ ^ 2 : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ)))
    exact hsquare.ofReal (𝕜 := ℂ)
  have hevenPoint (r : ℝ) : wB (2 * |r|) =
      (Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) * actualSuzukiEvenBProfile F r := by
    dsimp [wB, actualSuzukiEvenBProfile]
    rw [show (5 / 4 : ℝ) * (2 * |r|) = (5 / 2 : ℝ) * |r| by ring]
  have hevenSquare : Integrable (fun r : ℝ => ‖wB (2 * |r|)‖ ^ 2) volume := by
    simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using
      (even_double_l1_mass (fun t : ℝ => ((‖wB t‖ ^ 2 : ℝ) : ℂ)) hsquareC).1.re
  have hweighted : MemLp (fun r : ℝ => (Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) *
      actualSuzukiEvenBProfile F r) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm
      ((show Continuous (fun r : ℝ => (Real.exp ((5 / 2 : ℝ) * |r|) : ℂ)) by
        fun_prop).aestronglyMeasurable.mul hfull1.aestronglyMeasurable)).2
    exact hevenSquare.congr (Eventually.of_forall fun r => by
      change ‖wB (2 * |r|)‖ ^ 2 =
        ‖(Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) * actualSuzukiEvenBProfile F r‖ ^ 2
      rw [hevenPoint r])
  have hord : MemLp (actualSuzukiEvenBProfile F) 2 volume := by
    apply hweighted.mono hfull1.aestronglyMeasurable
    exact Eventually.of_forall fun r => by
      have he : 1 ≤ Real.exp ((5 / 2 : ℝ) * |r|) :=
        Real.one_le_exp_iff.mpr (by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact le_mul_of_one_le_left (norm_nonneg _) he
  refine ⟨hfull1, hord, hweighted, ?_⟩
  have hvSq := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hRvSq := (memLp_two_iff_integrable_sq_norm hRv.aestronglyMeasurable).1 hRv
  have hBpoint (t : ℝ) : ‖wB t‖ ^ 2 ≤
      2 * ‖v t‖ ^ 2 + (9 / 2 : ℝ) *
        ‖RightExponentialTail.rightExponentialTail (5 / 2) v t‖ ^ 2 := by
    have hn : ‖wB t‖ ≤ ‖v t‖ + (3 / 2 : ℝ) *
        ‖RightExponentialTail.rightExponentialTail (5 / 2) v t‖ := by
      calc
        _ ≤ ‖v t‖ + ‖(3 / 2 : ℂ) *
            RightExponentialTail.rightExponentialTail (5 / 2) v t‖ := by
          rw [hwB_eq t]
          exact norm_sub_le _ _
        _ = _ := by rw [norm_mul]; norm_num
    have hn2 := pow_le_pow_left₀ (norm_nonneg (wB t)) hn 2
    nlinarith [hn2, norm_nonneg (wB t), norm_nonneg (v t),
      norm_nonneg (RightExponentialTail.rightExponentialTail (5 / 2) v t),
      sq_nonneg (‖v t‖ - (3 / 2 : ℝ) *
        ‖RightExponentialTail.rightExponentialTail (5 / 2) v t‖)]
  have hBmass : (∫ t : ℝ in Ioi 0, ‖wB t‖ ^ 2) ≤
      (68 / 25 : ℝ) * ∫ t : ℝ in Ioi 0, ‖v t‖ ^ 2 := by
    have hmono := integral_mono hsquare
      ((hvSq.const_mul 2).add (hRvSq.const_mul (9 / 2 : ℝ))) hBpoint
    change (∫ t : ℝ in Ioi 0, ‖wB t‖ ^ 2) ≤
      ∫ t : ℝ in Ioi 0, 2 * ‖v t‖ ^ 2 + (9 / 2 : ℝ) *
        ‖RightExponentialTail.rightExponentialTail (5 / 2) v t‖ ^ 2 at hmono
    rw [integral_add (hvSq.const_mul 2) (hRvSq.const_mul (9 / 2 : ℝ)),
      integral_const_mul, integral_const_mul] at hmono
    norm_num at hRvMass
    linarith
  have hevenMass : (∫ r : ℝ,
      ‖(Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) * actualSuzukiEvenBProfile F r‖ ^ 2) =
      ∫ t : ℝ in Ioi 0, ‖wB t‖ ^ 2 := by
    have hmass := congrArg Complex.re
      (even_double_l1_mass (fun t : ℝ => ((‖wB t‖ ^ 2 : ℝ) : ℂ)) hsquareC).2
    simp only [integral_complex_ofReal, Complex.ofReal_re] at hmass
    simpa only [hevenPoint] using hmass
  have htheta : (∫ x : ℝ in Ioi Real.pi,
      (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2) ≤
      (∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) ^ 2 *
        (∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) := by
    obtain ⟨hU, hbound⟩ := actual_fullTheta_excess_memLp_norm
      0 (by norm_num) (by norm_num) F hF
    have hboundMass : thetaExcessMass 0 (fullTheta F) ≤
        (∑' j : ℕ, thetaModeCoefficient j) ^ 2 * thetaExcessMass 0 F := by
      rw [thetaExcess_mass_eq_sq_norm 0 (by norm_num) _ hU,
        thetaExcess_mass_eq_sq_norm 0 (by norm_num) F
          (h6_thetaExcess_memLp 0 (by norm_num) F hF)]
      exact (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans_eq (mul_pow _ _ 2)
    simpa only [thetaExcessMass, thetaExcessDensity, thetaModeCoefficient, sub_zero]
      using hboundMass
  have hraw : (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2) =
      Real.pi ^ (6 : ℕ) * ∫ x : ℝ in Ioi Real.pi,
        (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by field_simp [Real.pi_ne_zero]
  have hpi : Real.pi ^ (-(5 / 2 : ℝ)) * Real.pi ^ (6 : ℕ) =
      Real.pi ^ (7 / 2 : ℝ) := by
    rw [← Real.rpow_natCast Real.pi 6, ← Real.rpow_add Real.pi_pos]
    norm_num
  calc
    _ = ∫ t : ℝ in Ioi 0, ‖wB t‖ ^ 2 := hevenMass
    _ ≤ (68 / 25 : ℝ) * ∫ t : ℝ in Ioi 0, ‖v t‖ ^ 2 := hBmass
    _ = (68 / 25 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
        ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by
      rw [hvMass, hraw]
      calc
        _ = (68 / 25 : ℝ) *
            (Real.pi ^ (-(5 / 2 : ℝ)) * Real.pi ^ (6 : ℕ)) *
            ∫ x : ℝ in Ioi Real.pi,
              (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by ring
        _ = _ := by rw [hpi]
    _ ≤ _ := by
      have hc : 0 ≤ (68 / 25 : ℝ) * Real.pi ^ (7 / 2 : ℝ) := by positivity
      exact (mul_le_mul_of_nonneg_left htheta hc).trans_eq (by ring)

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
