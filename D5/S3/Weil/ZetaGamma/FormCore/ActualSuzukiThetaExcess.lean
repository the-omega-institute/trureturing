/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess
   mirror-E: none(waiver:analytic-theta-excess-estimate)
   anchors: []
   utility: none
   digest: Original physical H6 preserves the complete theta transform and bounds its sixth-moment excess. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open scoped ENNReal Topology

private def thetaExcessDensity (b x : ℝ) : ℝ := (x / Real.pi) ^ (6 : ℕ) - b
private def thetaExcessMeasure (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi Real.pi)).withDensity
    (fun x => ENNReal.ofReal (thetaExcessDensity b x))
private def thetaExcessMass (b : ℝ) (F : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ in Ioi Real.pi, thetaExcessDensity b x * ‖F x‖ ^ 2
private def thetaModeCoefficient (j : ℕ) : ℝ :=
  ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹

private theorem thetaExcessDensity_continuous (b : ℝ) : Continuous (thetaExcessDensity b) := by
  unfold thetaExcessDensity
  fun_prop

private theorem thetaExcessDensity_nonneg {b x : ℝ} (hb : b ≤ 1) (hx : Real.pi ≤ x) :
    0 ≤ thetaExcessDensity b x := by
  have h : 1 ≤ x / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by simpa using hx)
  exact sub_nonneg.mpr (hb.trans (one_le_pow₀ h))

private theorem thetaExcessDensity_scale (b a x : ℝ) :
    thetaExcessDensity b (a ^ 2 * x) =
      a ^ 12 * thetaExcessDensity b x + b * (a ^ 12 - 1) := by
  unfold thetaExcessDensity
  ring

private theorem thetaExcess_integrable_iff (b : ℝ) (hb : b ≤ 1) (f : ℝ → ℂ) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) (thetaExcessMeasure b) ↔
    Integrable (fun x : ℝ => thetaExcessDensity b x * ‖f x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
  unfold thetaExcessMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (thetaExcessDensity_continuous b).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [ENNReal.toReal_ofReal (thetaExcessDensity_nonneg hb hx.le), smul_eq_mul]

private theorem thetaExcess_mass_eq_sq_norm
    (b : ℝ) (hb : b ≤ 1) (f : ℝ → ℂ) (hf : MemLp f 2 (thetaExcessMeasure b)) :
    thetaExcessMass b f = ‖hf.toLp f‖ ^ 2 := by
  have hchange :
      thetaExcessMass b f = ∫ x : ℝ, ‖f x‖ ^ 2 ∂thetaExcessMeasure b := by
    unfold thetaExcessMass thetaExcessMeasure
    rw [integral_withDensity_eq_integral_toReal_smul
      (thetaExcessDensity_continuous b).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [ENNReal.toReal_ofReal (thetaExcessDensity_nonneg hb hx.le), smul_eq_mul]
  rw [hchange]
  calc
    _ = ∫ x : ℝ, ‖hf.toLp f x‖ ^ 2 ∂thetaExcessMeasure b := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        (real_inner_self_eq_norm_sq (hf.toLp f x)).symm
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _

private theorem h6_thetaExcess_memLp (b : ℝ) (hb : b ≤ 1)
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    MemLp F 2 (thetaExcessMeasure b) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hF.1.aestronglyMeasurable).1 hF.1
  have hd : Integrable (fun x : ℝ => thetaExcessDensity b x * ‖F x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    convert hF.2.sub (hsq.const_mul b) using 1
    funext x
    dsimp [thetaExcessDensity]
    ring
  apply (memLp_two_iff_integrable_sq_norm
    (hF.1.aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _))).2
  exact (thetaExcess_integrable_iff b hb F).2 hd

private theorem physicalTerm_aestronglyMeasurable
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (j : ℕ) :
    AEStronglyMeasurable (physicalTerm F j) (volume.restrict (Ioi Real.pi)) := by
  let a : ℝ := (j + 1 : ℕ)
  have ha : 1 ≤ a := by dsimp [a]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have ha0 : 0 < a := by linarith
  let G : ℝ → ℂ := (Ioi Real.pi).indicator F
  have hG : MemLp G 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hF.1
  have hc : AEStronglyMeasurable (fun x : ℝ => G (a ^ 2 * x)) volume := by
    simpa only [smul_eq_mul, Function.comp_def] using
      hG.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_smul volume (pow_ne_zero 2 ha0.ne'))
  have heq : (fun x : ℝ => G (a ^ 2 * x)) =ᵐ[volume.restrict (Ioi Real.pi)]
      (fun x : ℝ => F (a ^ 2 * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := Real.pi_pos.trans hx
    have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
    have hax : Real.pi < a ^ 2 * x :=
      hx.trans_le (le_mul_of_one_le_left hx0.le ha2)
    exact Set.indicator_of_mem hax F
  have hfc := hc.restrict.congr heq
  convert hfc.const_mul (((j + 1 : ℕ) : ℂ) ^ (4 : ℕ)) using 1
  rfl

private theorem physicalTerm_norm_sq (F : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    ‖physicalTerm F j x‖ ^ 2 =
      (((j + 1 : ℕ) : ℝ) ^ (8 : ℕ)) *
        ‖F ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x)‖ ^ 2 := by
  simp only [physicalTerm, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  ring

private theorem physicalTerm_h6
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (j : ℕ) :
    originalPhysicalH6 (physicalTerm F j) := by
  let a : ℝ := (j + 1 : ℕ)
  have ha : 1 ≤ a := by dsimp [a]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a ^ 2 := pow_pos ha0 2
  have hpi : Real.pi ≤ a ^ 2 * Real.pi := by
    nlinarith [one_le_pow₀ (n := 2) ha, Real.pi_pos]
  let h : ℝ → ℝ := fun x => (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2
  have htail : IntegrableOn h (Ioi (a ^ 2 * Real.pi)) :=
    IntegrableOn.mono_set hF.2 (Ioi_subset_Ioi hpi)
  have hcomp : IntegrableOn (fun x : ℝ => h (a ^ 2 * x)) (Ioi Real.pi) :=
    (integrableOn_Ioi_comp_mul_left_iff h Real.pi ha2).2 htail
  have hmoment : Integrable
      (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) * ‖physicalTerm F j x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    convert hcomp.const_mul ((a ^ 4)⁻¹) using 1
    funext x
    rw [physicalTerm_norm_sq]
    dsimp [h, a]
    field_simp
  have hmeas := physicalTerm_aestronglyMeasurable F hF j
  have hsq : Integrable (fun x : ℝ => ‖physicalTerm F j x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    apply hmoment.mono' (hmeas.norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hxp : 1 ≤ x / Real.pi :=
      (le_div_iff₀ Real.pi_pos).2 (by simpa only [one_mul] using hx.le)
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hxp)
  exact ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 hsq, hmoment⟩

private theorem physicalTerm_excess_mass_le
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (j : ℕ) :
    thetaExcessMass b (physicalTerm F j) ≤
      thetaModeCoefficient j ^ 2 * thetaExcessMass b F := by
  let a : ℝ := (j + 1 : ℕ)
  have ha : 1 ≤ a := by dsimp [a]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a ^ 2 := pow_pos ha0 2
  have hpi : Real.pi ≤ a ^ 2 * Real.pi := by
    nlinarith [one_le_pow₀ (n := 2) ha, Real.pi_pos]
  let h : ℝ → ℝ := fun x => thetaExcessDensity b x * ‖F x‖ ^ 2
  have hi : Integrable h (volume.restrict (Ioi Real.pi)) :=
    (thetaExcess_integrable_iff b hb1 F).1
      ((memLp_two_iff_integrable_sq_norm
        (h6_thetaExcess_memLp b hb1 F hF).aestronglyMeasurable).1
          (h6_thetaExcess_memLp b hb1 F hF))
  have htail : IntegrableOn h (Ioi (a ^ 2 * Real.pi)) :=
    IntegrableOn.mono_set hi (Ioi_subset_Ioi hpi)
  have hcomp : IntegrableOn (fun x : ℝ => h (a ^ 2 * x)) (Ioi Real.pi) :=
    (integrableOn_Ioi_comp_mul_left_iff h Real.pi ha2).2 htail
  have himode : Integrable
      (fun x : ℝ => thetaExcessDensity b x * ‖physicalTerm F j x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) :=
    (thetaExcess_integrable_iff b hb1 _).1
      ((memLp_two_iff_integrable_sq_norm
        (h6_thetaExcess_memLp b hb1 _ (physicalTerm_h6 F hF j)).aestronglyMeasurable).1
          (h6_thetaExcess_memLp b hb1 _ (physicalTerm_h6 F hF j)))
  have hpoint (x : ℝ) :
      thetaExcessDensity b x * ‖physicalTerm F j x‖ ^ 2 ≤
        (a ^ 4)⁻¹ * h (a ^ 2 * x) := by
    have hq : a ^ 12 * thetaExcessDensity b x ≤ thetaExcessDensity b (a ^ 2 * x) := by
      rw [thetaExcessDensity_scale]
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr (one_le_pow₀ (n := 12) ha))]
    have hh := mul_le_mul_of_nonneg_right hq
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha0.le 4))
        (sq_nonneg ‖F (a ^ 2 * x)‖))
    convert hh using 1
    · rw [physicalTerm_norm_sq]
      dsimp [a]
      field_simp
    · dsimp [h]
      ring
  have htail_le :
      (∫ x : ℝ in Ioi (a ^ 2 * Real.pi), h x) ≤ thetaExcessMass b F := by
    exact integral_mono_measure
      (Measure.restrict_mono (Ioi_subset_Ioi hpi) le_rfl)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (thetaExcessDensity_nonneg hb1 hx.le) (sq_nonneg _)) hi
  calc
    thetaExcessMass b (physicalTerm F j) ≤
        ∫ x : ℝ in Ioi Real.pi, (a ^ 4)⁻¹ * h (a ^ 2 * x) :=
      integral_mono himode (hcomp.const_mul _) hpoint
    _ = (a ^ 4)⁻¹ * (a ^ 2)⁻¹ *
        (∫ x : ℝ in Ioi (a ^ 2 * Real.pi), h x) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi h Real.pi ha2]
      simp only [smul_eq_mul]
      ring
    _ ≤ (a ^ 4)⁻¹ * (a ^ 2)⁻¹ * thetaExcessMass b F :=
      mul_le_mul_of_nonneg_left htail_le (by positivity)
    _ = thetaModeCoefficient j ^ 2 * thetaExcessMass b F := by
      dsimp [thetaModeCoefficient, a]
      field_simp

private theorem thetaModeCoefficient_summable : Summable thetaModeCoefficient := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℕ))⁻¹) :=
    (Real.summable_nat_pow_inv (p := 3)).2 (by norm_num)
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (3 : ℕ))⁻¹) 1).2 h

private theorem actual_fullTheta_excess_memLp_norm
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    ∃ hU : MemLp (fullTheta F) 2 (thetaExcessMeasure b),
      ‖hU.toLp (fullTheta F)‖ ≤
        (∑' j : ℕ, thetaModeCoefficient j) *
          ‖(h6_thetaExcess_memLp b hb1 F hF).toLp F‖ := by
  let f0 : Lp ℂ 2 (thetaExcessMeasure b) := (h6_thetaExcess_memLp b hb1 F hF).toLp F
  let fj : ℕ → Lp ℂ 2 (thetaExcessMeasure b) := fun j =>
    (h6_thetaExcess_memLp b hb1 _ (physicalTerm_h6 F hF j)).toLp (physicalTerm F j)
  have hnorm (j : ℕ) : ‖fj j‖ ≤ thetaModeCoefficient j * ‖f0‖ := by
    have hm := physicalTerm_excess_mass_le b hb0 hb1 F hF j
    rw [thetaExcess_mass_eq_sq_norm b hb1 _ (h6_thetaExcess_memLp b hb1 _ (physicalTerm_h6 F hF j)),
      thetaExcess_mass_eq_sq_norm b hb1 F (h6_thetaExcess_memLp b hb1 F hF)] at hm
    have hc : 0 ≤ thetaModeCoefficient j := by unfold thetaModeCoefficient; positivity
    change ‖fj j‖ ^ 2 ≤ thetaModeCoefficient j ^ 2 * ‖f0‖ ^ 2 at hm
    rw [← mul_pow] at hm
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1 hm
  have hnormsum : Summable (fun j : ℕ => ‖fj j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      (thetaModeCoefficient_summable.mul_right ‖f0‖)
  have henormsum : (∑' j : ℕ, ‖fj j‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.2 hnormsum
  let S : Lp ℂ 2 (thetaExcessMeasure b) := ∑' j : ℕ, fj j
  have hbridge : (fun x : ℝ => S x) =ᵐ[thetaExcessMeasure b] fullTheta F := by
    have hseries := Lp.coeFn_tsum henormsum
    have hterms : ∀ᵐ x : ℝ ∂thetaExcessMeasure b,
        ∀ j : ℕ, fj j x = physicalTerm F j x := by
      exact ae_all_iff.2 fun j =>
        (h6_thetaExcess_memLp b hb1 _ (physicalTerm_h6 F hF j)).coeFn_toLp
    filter_upwards [hseries, hterms] with x hx hxt
    exact hx.trans (tsum_congr hxt)
  have hU : MemLp (fullTheta F) 2 (thetaExcessMeasure b) :=
    (memLp_congr_ae hbridge).1 (Lp.memLp S)
  have htoLp : hU.toLp (fullTheta F) = S := by
    apply Lp.ext
    exact hU.coeFn_toLp.trans hbridge.symm
  refine ⟨hU, ?_⟩
  rw [htoLp]
  calc
    ‖S‖ ≤ ∑' j : ℕ, ‖fj j‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' j : ℕ, thetaModeCoefficient j * ‖f0‖ :=
      Summable.tsum_le_tsum hnorm hnormsum
        (thetaModeCoefficient_summable.mul_right ‖f0‖)
    _ = (∑' j : ℕ, thetaModeCoefficient j) * ‖f0‖ := tsum_mul_right

/-- The literal complete theta transform preserves the normalized sixth-moment
excess, with the exact cubically summable dilation constant. Both integrability
and the bound are proved from originalPhysicalH6; no assumed theta convergence
or desired excess estimate is supplied as a premise. -/
theorem actual_h6_fullTheta_excess_bound
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    originalPhysicalH6 (fullTheta F) ∧
    Integrable
      (fun x : ℝ => ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) ∧
    (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2) ≤
      (∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) ^ 2 *
        (∫ x : ℝ in Ioi Real.pi,
          ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) := by
  obtain ⟨hU0, _⟩ := actual_fullTheta_excess_memLp_norm 0 (by norm_num) (by norm_num) F hF
  have hmeasure : volume.restrict (Ioi Real.pi) ≤ thetaExcessMeasure 0 := by
    have hden : (fun _ : ℝ => (1 : ℝ≥0∞)) ≤ᵐ[volume.restrict (Ioi Real.pi)]
        (fun x => ENNReal.ofReal (thetaExcessDensity 0 x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpi : 1 ≤ x / Real.pi :=
        (le_div_iff₀ Real.pi_pos).2 (by simpa only [one_mul] using hx.le)
      have hxpow : 1 ≤ (x / Real.pi) ^ (6 : ℕ) := one_le_pow₀ hxpi
      simpa only [thetaExcessDensity, sub_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal hxpow
    exact withDensity_one.symm.trans_le (withDensity_mono hden)
  have hUoriginal : originalPhysicalH6 (fullTheta F) := by
    refine ⟨hU0.mono_measure hmeasure, ?_⟩
    simpa only [thetaExcessDensity, sub_zero] using
      (thetaExcess_integrable_iff 0 (by norm_num) _).1
        ((memLp_two_iff_integrable_sq_norm hU0.aestronglyMeasurable).1 hU0)
  obtain ⟨hU, hbound⟩ := actual_fullTheta_excess_memLp_norm 1 (by norm_num) le_rfl F hF
  refine ⟨hUoriginal, (thetaExcess_integrable_iff 1 le_rfl _).1
    ((memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).1 hU), ?_⟩
  change thetaExcessMass 1 (fullTheta F) ≤
    (∑' j : ℕ, thetaModeCoefficient j) ^ 2 * thetaExcessMass 1 F
  rw [thetaExcess_mass_eq_sq_norm 1 le_rfl _ hU,
    thetaExcess_mass_eq_sq_norm 1 le_rfl F (h6_thetaExcess_memLp 1 le_rfl F hF)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans_eq (mul_pow _ _ 2)

/-- H6 makes the literal physical mode series summable almost everywhere
on the original half-line. This is proved in the weighted L2 space, then
transported through its strictly positive density. -/
theorem actual_h6_physicalTerm_summable_ae
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi), Summable (fun j : ℕ => physicalTerm F j x) := by
  let f0 : Lp ℂ 2 (thetaExcessMeasure 0) :=
    (h6_thetaExcess_memLp 0 (by norm_num) F hF).toLp F
  let fj : ℕ → Lp ℂ 2 (thetaExcessMeasure 0) := fun j =>
    (h6_thetaExcess_memLp 0 (by norm_num) _ (physicalTerm_h6 F hF j)).toLp (physicalTerm F j)
  have hnorm (j : ℕ) : ‖fj j‖ ≤ thetaModeCoefficient j * ‖f0‖ := by
    have hm := physicalTerm_excess_mass_le 0 (by norm_num) (by norm_num) F hF j
    rw [thetaExcess_mass_eq_sq_norm 0 (by norm_num) _
        (h6_thetaExcess_memLp 0 (by norm_num) _ (physicalTerm_h6 F hF j)),
      thetaExcess_mass_eq_sq_norm 0 (by norm_num) F
        (h6_thetaExcess_memLp 0 (by norm_num) F hF)] at hm
    have hc : 0 ≤ thetaModeCoefficient j := by unfold thetaModeCoefficient; positivity
    change ‖fj j‖ ^ 2 ≤ thetaModeCoefficient j ^ 2 * ‖f0‖ ^ 2 at hm
    rw [← mul_pow] at hm
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1 hm
  have hnormsum : Summable (fun j : ℕ => ‖fj j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      (thetaModeCoefficient_summable.mul_right ‖f0‖)
  have henormsum : (∑' j : ℕ, ‖fj j‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.2 hnormsum
  have hpoint : ∀ᵐ x : ℝ ∂thetaExcessMeasure 0,
      Summable (fun j : ℕ => physicalTerm F j x) := by
    have hseries := Lp.hasSum_coeFn_tsum henormsum
    have hterms : ∀ᵐ x : ℝ ∂thetaExcessMeasure 0,
        ∀ j : ℕ, fj j x = physicalTerm F j x := by
      exact ae_all_iff.2 fun j =>
        (h6_thetaExcess_memLp 0 (by norm_num) _ (physicalTerm_h6 F hF j)).coeFn_toLp
    filter_upwards [hseries, hterms] with x hx hxt
    exact hx.summable.congr hxt
  have hden : ∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi),
      ENNReal.ofReal (thetaExcessDensity 0 x) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := Real.pi_pos.trans hx
    exact (ENNReal.ofReal_pos.mpr (by
      dsimp [thetaExcessDensity]
      exact sub_pos.mpr (pow_pos (div_pos hx0 Real.pi_pos) 6))).ne'
  have hac : volume.restrict (Ioi Real.pi) ≪ thetaExcessMeasure 0 :=
    withDensity_absolutelyContinuous'
      (thetaExcessDensity_continuous 0).measurable.ennreal_ofReal.aemeasurable hden
  exact hac.ae_le hpoint


end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
