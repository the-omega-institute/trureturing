/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-mean-charge-helper)
   anchors: []
   utility: none
   digest: Explicit bounded-kernel representation of the actual even-B mean. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace

/-! The original full-line even-B mean has a bounded-kernel representation.
Its linearity is established directly from H6 source combinations through
the complete theta series and its physical moments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open scoped Topology ENNReal

def actualSuzukiMeanKernel (t : ℝ) : ℝ :=
  (6 * Real.exp (-(5 / 4 : ℝ) * t) - 1) / 5

def actualSuzukiMeanCharge (F : ℝ → ℂ) : ℂ :=
  ∫ r : ℝ, actualSuzukiEvenBProfile F r

private theorem meanKernel_bounds (t : ℝ) (ht : 0 ≤ t) :
    -(1 / 5 : ℝ) ≤ actualSuzukiMeanKernel t ∧ actualSuzukiMeanKernel t ≤ 1 := by
  have he₀ := Real.exp_nonneg (-(5 / 4 : ℝ) * t)
  have he₁ : Real.exp (-(5 / 4 : ℝ) * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  unfold actualSuzukiMeanKernel
  constructor <;> nlinarith

private theorem meanKernel_norm_le (t : ℝ) (ht : 0 ≤ t) :
    ‖(actualSuzukiMeanKernel t : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(meanKernel_bounds t ht).1],
    (meanKernel_bounds t ht).2⟩

private theorem meanKernel_mul_integrable (u : ℝ → ℂ)
    (hu : IntegrableOn u (Ioi (0 : ℝ))) :
    IntegrableOn (fun t => (actualSuzukiMeanKernel t : ℂ) * u t)
      (Ioi (0 : ℝ)) := by
  have hm : Continuous (fun t => (actualSuzukiMeanKernel t : ℂ)) := by
    unfold actualSuzukiMeanKernel
    fun_prop
  apply hu.bdd_mul (c := 1) hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact meanKernel_norm_le t (show 0 < t from ht).le

/-- The actual integral is genuine L1, and equals the literal bounded-kernel
integral of the SAME actual complete-theta profile. -/
theorem actual_h6_suzuki_mean_charge_formula
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    Integrable (actualSuzukiEvenBProfile F) volume ∧
      actualSuzukiMeanCharge F =
        ∫ t : ℝ in Ioi 0,
          (actualSuzukiMeanKernel t : ℂ) * actualGammaProfile F t := by
  let u := actualGammaProfile F
  have hu : IntegrableOn u (Ioi (0 : ℝ)) :=
    (actual_h6_gamma_profile_l1_l2 F hF).1
  obtain ⟨hR, hRmass⟩ := right_exponential_tail_l1_integrable_and_mass
    (by norm_num : (0 : ℝ) < 5 / 4) u hu
  have hB : IntegrableOn (actualSuzukiBProfile F) (Ioi (0 : ℝ)) :=
    hu.sub (hR.const_mul (3 / 2 : ℂ))
  have heven := even_double_l1_mass (actualSuzukiBProfile F) hB
  refine ⟨heven.1, ?_⟩
  have hE : IntegrableOn (fun t =>
      (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * u t) (Ioi (0 : ℝ)) := by
    have hm : Continuous (fun t : ℝ =>
        (Real.exp (-(5 / 4 : ℝ) * t) : ℂ)) := by fun_prop
    apply hu.bdd_mul (c := 1) hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by have := (show 0 < t from ht); nlinarith)
  have hRmass' :
      (∫ t : ℝ in Ioi 0, rightExponentialTail (5 / 4) u t) =
        (4 / 5 : ℂ) * ((∫ t : ℝ in Ioi 0, u t) -
          rightExponentialTail (5 / 4) u 0) := by
    convert hRmass using 1
    norm_num
  have hμ : actualSuzukiMeanCharge F =
      (∫ t : ℝ in Ioi 0, u t) - (3 / 2 : ℂ) *
        (∫ t : ℝ in Ioi 0, rightExponentialTail (5 / 4) u t) := by
    change (∫ r : ℝ, actualSuzukiBProfile F (2 * |r|)) = _
    rw [heven.2]
    change (∫ t : ℝ in Ioi 0,
      u t - (3 / 2 : ℂ) * rightExponentialTail (5 / 4) u t) = _
    rw [integral_sub hu (hR.const_mul _), integral_const_mul]
  calc
    actualSuzukiMeanCharge F =
        (6 / 5 : ℂ) * rightExponentialTail (5 / 4) u 0 -
          (1 / 5 : ℂ) * (∫ t : ℝ in Ioi 0, u t) := by
      rw [hμ, hRmass']
      ring
    _ = ∫ t : ℝ in Ioi 0,
        (6 / 5 : ℂ) * ((Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * u t) -
          (1 / 5 : ℂ) * u t := by
      rw [integral_sub (hE.const_mul _) (hu.const_mul _),
        integral_const_mul, integral_const_mul]
      simp only [rightExponentialTail, zero_add]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp [actualSuzukiMeanKernel, u]
        push_cast
        ring

/-- The explicit charge has L1 operator bound one; no endpoint trace is
discarded and no Fourier form-domain assumption is needed. -/
theorem actual_h6_suzuki_mean_charge_norm_le
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    ‖actualSuzukiMeanCharge F‖ ≤
      ∫ t : ℝ in Ioi 0, ‖actualGammaProfile F t‖ := by
  have hu := (actual_h6_gamma_profile_l1_l2 F hF).1
  have hw := meanKernel_mul_integrable (actualGammaProfile F) hu
  rw [(actual_h6_suzuki_mean_charge_formula F hF).2]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0,
        ‖(actualSuzukiMeanKernel t : ℂ) * actualGammaProfile F t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono_ae hw.norm hu.norm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (meanKernel_norm_le t (show 0 < t from ht).le)
        (norm_nonneg (actualGammaProfile F t))

/-- Real-valuedness of the actual charge needs only AE real-valuedness of
the actual profile, with its H6-derived L1 domain retained. -/
theorem actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hreal : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (actualGammaProfile F t).im = 0) :
    (actualSuzukiMeanCharge F).im = 0 := by
  have hw := meanKernel_mul_integrable (actualGammaProfile F)
    (actual_h6_gamma_profile_l1_l2 F hF).1
  rw [(actual_h6_suzuki_mean_charge_formula F hF).2]
  calc
    _ = ∫ t : ℝ in Ioi 0,
        ((actualSuzukiMeanKernel t : ℂ) * actualGammaProfile F t).im := by
      symm
      simpa only [RCLike.im_eq_complex_im] using (integral_im hw)
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hreal] with t ht
      simp [Complex.mul_im, ht]

/-- Actual charge linearity follows from a genuine AE relation between
the three profiles, with all actual L1 domains paid by their H6 sources.
Complex coefficients are allowed, including the real cancellation case. -/
theorem actual_h6_suzuki_mean_charge_linear_of_profile_ae
    (F G H : ℝ → ℂ)
    (hF : originalPhysicalH6 F) (hG : originalPhysicalH6 G)
    (hH : originalPhysicalH6 H) (a b : ℂ)
    (hprofile : actualGammaProfile H =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => a * actualGammaProfile F t + b * actualGammaProfile G t)) :
    actualSuzukiMeanCharge H =
      a * actualSuzukiMeanCharge F + b * actualSuzukiMeanCharge G := by
  have hwF := meanKernel_mul_integrable (actualGammaProfile F)
    (actual_h6_gamma_profile_l1_l2 F hF).1
  have hwG := meanKernel_mul_integrable (actualGammaProfile G)
    (actual_h6_gamma_profile_l1_l2 G hG).1
  rw [(actual_h6_suzuki_mean_charge_formula H hH).2,
    (actual_h6_suzuki_mean_charge_formula F hF).2,
    (actual_h6_suzuki_mean_charge_formula G hG).2]
  calc
    _ = ∫ t : ℝ in Ioi 0,
        a * ((actualSuzukiMeanKernel t : ℂ) * actualGammaProfile F t) +
          b * ((actualSuzukiMeanKernel t : ℂ) * actualGammaProfile G t) := by
      apply integral_congr_ae
      filter_upwards [hprofile] with t ht
      rw [ht]
      ring
    _ = _ := by
      rw [integral_add (hwF.const_mul a) (hwG.const_mul b),
        integral_const_mul, integral_const_mul]

private theorem fullTheta_ae_linear
    (F G : ℝ → ℂ) (hF : originalPhysicalH6 F) (hG : originalPhysicalH6 G)
    (a b : ℂ) :
    fullTheta (fun x => a * F x + b * G x) =ᵐ[volume.restrict (Ioi Real.pi)]
      (fun x => a * fullTheta F x + b * fullTheta G x) := by
  filter_upwards [actual_h6_physicalTerm_summable_ae F hF,
    actual_h6_physicalTerm_summable_ae G hG] with x hxF hxG
  have hs : HasSum (fun j => physicalTerm (fun y => a * F y + b * G y) j x)
      (a * fullTheta F x + b * fullTheta G x) := by
    convert (hxF.hasSum.mul_left a).add (hxG.hasSum.mul_left b) using 1
    · funext j
      simp only [physicalTerm]
      ring
    · rfl
  exact hs.tsum_eq

private theorem fullTheta_weighted_moment_linear
    (F G : ℝ → ℂ) (hF : originalPhysicalH6 F) (hG : originalPhysicalH6 G)
    (a b : ℂ) (β : ℝ) (hβ : β < 5 / 2) :
    (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) *
      fullTheta (fun y => a * F y + b * G y) x) =
        a * (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * fullTheta F x) +
          b * (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * fullTheta G x) := by
  have hiF := physical_h6_weighted_l1 (fullTheta F)
    (actual_h6_fullTheta_excess_bound F hF).1 β hβ
  have hiG := physical_h6_weighted_l1 (fullTheta G)
    (actual_h6_fullTheta_excess_bound G hG).1 β hβ
  calc
    _ = ∫ x : ℝ in Ioi Real.pi,
        a * (((x ^ β : ℝ) : ℂ) * fullTheta F x) +
          b * (((x ^ β : ℝ) : ℂ) * fullTheta G x) := by
      apply integral_congr_ae
      filter_upwards [fullTheta_ae_linear F G hF hG a b] with x hx
      rw [hx]
      ring
    _ = _ := by
      rw [integral_add (hiF.const_mul a) (hiG.const_mul b),
        integral_const_mul, integral_const_mul]

private theorem meanCharge_physical_moment_formula
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    actualSuzukiMeanCharge F =
      (6 / 5 : ℂ) * ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        (∫ x : ℝ in Ioi Real.pi, fullTheta F x) -
      (1 / 5 : ℂ) *
        (∫ x : ℝ in Ioi Real.pi, ((x ^ (5 / 4 : ℝ) : ℝ) : ℂ) * fullTheta F x) := by
  obtain ⟨hu, hI, hR0⟩ := actual_profile_l1_and_physical_moments F hF
  obtain ⟨hR, hRmass⟩ := right_exponential_tail_l1_integrable_and_mass
    (by norm_num : (0 : ℝ) < 5 / 4) (actualGammaProfile F) hu
  have hB : IntegrableOn (actualSuzukiBProfile F) (Ioi (0 : ℝ)) :=
    hu.sub (hR.const_mul (3 / 2 : ℂ))
  change (∫ r : ℝ, actualSuzukiBProfile F (2 * |r|)) = _
  rw [(even_double_l1_mass _ hB).2]
  change (∫ t : ℝ in Ioi 0, actualGammaProfile F t -
    (3 / 2 : ℂ) * rightExponentialTail (5 / 4) (actualGammaProfile F) t) = _
  rw [integral_sub hu (hR.const_mul _), integral_const_mul, hRmass, hI, hR0]
  norm_num
  ring

/-- The original full-line even-B mean is linear in actual H6 source
combinations. The complete theta series is handled on its H6-derived
almost-everywhere summability set; no profile-linearity premise is assumed. -/
theorem actual_h6_suzuki_mean_charge_linear
    (F G : ℝ → ℂ) (hF : originalPhysicalH6 F) (hG : originalPhysicalH6 G)
    (a b : ℂ) (hH : originalPhysicalH6 (fun x => a * F x + b * G x)) :
    actualSuzukiMeanCharge (fun x => a * F x + b * G x) =
      a * actualSuzukiMeanCharge F + b * actualSuzukiMeanCharge G := by
  rw [meanCharge_physical_moment_formula _ hH,
    meanCharge_physical_moment_formula F hF, meanCharge_physical_moment_formula G hG,
    fullTheta_weighted_moment_linear F G hF hG a b (5 / 4) (by norm_num)]
  have hzero := fullTheta_weighted_moment_linear F G hF hG a b 0 (by norm_num)
  simp only [Real.rpow_zero, Complex.ofReal_one, one_mul] at hzero
  rw [hzero]
  ring

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
