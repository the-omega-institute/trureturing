/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed three-step defect and decreasing normalized iterates on the acquired flow. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelInputTests
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSuperharmonic
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open NativeFullResidual NativeBorelCommonFlow NativeBorelRepresentation NativeBorelTVTopology
open NativeConditionalControl.Tail

private theorem iterate_g_bound (F : CommonFlow) (n : ℕ) (Q : PDescriptor) :
    iterate F.L g n Q ≤ 1 := by
  induction n generalizing Q with
  | zero => exact prob_le_one
  | succ n ih =>
    calc
      _ ≤ ∫⁻ R, (1 : ℝ≥0∞) ∂F.L Q := lintegral_mono (fun R => ih R)
      _ ≤ ∫⁻ R, (1 : ℝ≥0∞) ∂F.C Q := lintegral_mono' (L_le_C F Q) (le_refl _)
      _ = 1 := by simp

private theorem normalized_g_finite (F : CommonFlow) (n : ℕ) (Q : PDescriptor) :
    normalizedIterate F g n Q ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.pow_ne_top
    exact ENNReal.inv_ne_top.mpr (by norm_num [endpointRate])
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (iterate_g_bound F n Q)

private theorem normalized_g_real_bound (F : CommonFlow) (n : ℕ) (Q : PDescriptor) :
    (normalizedIterate F g n Q).toReal ≤ (25 / 6 : ℝ) ^ n := by
  have hb : normalizedIterate F g n Q ≤ endpointRate⁻¹ ^ n := by
    simpa only [normalizedIterate, mul_one] using mul_le_mul_of_nonneg_left (iterate_g_bound F n Q) (bot_le : 0 ≤ endpointRate⁻¹ ^ n)
  have hf : endpointRate⁻¹ ^ n ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num [endpointRate]))
  have hr := ENNReal.toReal_mono hf hb
  simpa [ENNReal.toReal_pow, ENNReal.toReal_inv, endpointRate] using hr

theorem h_finite (F : CommonFlow) (Q : PDescriptor) :
    threeStepAverage F Q ≠ ∞ := by
  unfold threeStepAverage
  exact ENNReal.div_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨measure_ne_top (law Q) _, normalized_g_finite F 1 Q⟩,
      normalized_g_finite F 2 Q⟩) (by norm_num)

private theorem Th_finite (F : CommonFlow) (Q : PDescriptor) :
    normalizedAction F (threeStepAverage F) Q ≠ ∞ := by
  rw [normalizedAction_threeStepAverage]
  exact ENNReal.div_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨normalized_g_finite F 1 Q, normalized_g_finite F 2 Q⟩,
      normalized_g_finite F 3 Q⟩) (by norm_num)

def excess (Q : PDescriptor) : ℝ := (g Q).toReal - 9 / 25
def h (F : CommonFlow) (Q : PDescriptor) : ℝ := (threeStepAverage F Q).toReal
def delta (F : CommonFlow) (Q : PDescriptor) : ℝ :=
  h F Q - (normalizedAction F (threeStepAverage F) Q).toReal

private theorem h_real (F : CommonFlow) (Q : PDescriptor) :
    h F Q = ((g Q).toReal + (normalizedIterate F g 1 Q).toReal +
      (normalizedIterate F g 2 Q).toReal) / 3 := by
  unfold h threeStepAverage
  rw [ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨show g Q ≠ ∞ from measure_ne_top (law Q) _, normalized_g_finite F 1 Q⟩)
      (normalized_g_finite F 2 Q),
    ENNReal.toReal_add (show g Q ≠ ∞ from measure_ne_top (law Q) _)
      (normalized_g_finite F 1 Q)]
  norm_num

private theorem delta_real (F : CommonFlow) (Q : PDescriptor) :
    delta F Q = ((g Q).toReal - (normalizedIterate F g 3 Q).toReal) / 3 := by
  rw [delta, h_real, normalizedAction_threeStepAverage]
  rw [ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨normalized_g_finite F 1 Q, normalized_g_finite F 2 Q⟩) (normalized_g_finite F 3 Q),
    ENNReal.toReal_add (normalized_g_finite F 1 Q) (normalized_g_finite F 2 Q)]
  norm_num
  ring

private theorem normalized_g_ae_bound (F : CommonFlow) (n : ℕ) :
    ∀ᵐ Q ∂F.nuP, normalizedIterate F g n Q ≤ (10 / 9 : ℝ≥0∞) ^ n * (4 / 9) := by
  induction n with
  | zero =>
    filter_upwards [(common_flow_operator_bounds F).2] with Q hQ
    simpa [normalizedIterate, iterate] using hQ.2.1
  | succ n ih =>
    have hc := Measure.ae_ae_of_ae_comp (κ := F.C)
      ((common_flow_word_iteration F).1.symm ▸ ih)
    filter_upwards [hc] with Q hQ
    rw [normalizedIterate_succ F g measurable_g]
    unfold normalizedAction
    have hb : (∫⁻ R, normalizedIterate F g n R ∂F.L Q) ≤
        (4 / 15 : ℝ≥0∞) * ((10 / 9 : ℝ≥0∞) ^ n * (4 / 9)) := by
      calc
        _ ≤ ∫⁻ _ : PDescriptor, (10 / 9 : ℝ≥0∞) ^ n * (4 / 9) ∂F.L Q :=
          lintegral_mono_ae ((L_le_C F Q).absolutelyContinuous.ae_le hQ)
        _ ≤ ∫⁻ _ : PDescriptor, (10 / 9 : ℝ≥0∞) ^ n * (4 / 9)
            ∂(4 / 15 : ℝ≥0∞) • F.C Q :=
          lintegral_mono' ((common_flow_operator_bounds F).1 Q).2 (le_refl _)
        _ = _ := by simp [mul_comm]
    have hr : endpointRate⁻¹ * (4 / 15 : ℝ≥0∞) = 10 / 9 := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by norm_num [endpointRate]))
          (by finiteness)) (by finiteness)).mp
      norm_num [endpointRate, ENNReal.toReal_inv, ENNReal.toReal_mul]
    calc
      _ ≤ endpointRate⁻¹ * ((4 / 15 : ℝ≥0∞) * ((10 / 9 : ℝ≥0∞) ^ n * (4 / 9))) :=
        mul_le_mul_of_nonneg_left hb bot_le
      _ = _ := by rw [← mul_assoc, hr, pow_succ]; ring

/-- The defect is signed real subtraction; its lower bound follows from the original box. -/
theorem common_flow_signed_h (F : CommonFlow) :
    @Measurable _ _ (@borel _ (descriptorTVTopology .p)) inferInstance (h F) ∧
    ∀ᵐ Q ∂F.nuP, (3 / 25 : ℝ) ≤ h F Q ∧ h F Q ≤ 1 / 2 ∧
      0 ≤ excess Q ∧
      delta F Q = ((g Q).toReal - (normalizedIterate F g 3 Q).toReal) / 3 ∧
      excess Q / 3 ≤ delta F Q ∧
      normalizedAction F (threeStepAverage F) Q ≤ threeStepAverage F Q := by
  constructor
  · rw [descriptor_tv_borel_eq]
    exact (((measurable_g.add (measurable_normalizedIterate F g measurable_g 1)).add
      (measurable_normalizedIterate F g measurable_g 2)).div_const 3).ennreal_toReal
  · filter_upwards [(common_flow_operator_bounds F).2,
      common_flow_normalized_third_step F,
      normalized_g_ae_bound F 1, normalized_g_ae_bound F 2] with Q hg ht hb1 hb2
    have hgl := ENNReal.toReal_mono (measure_ne_top (law Q) _) hg.1
    have hgu : (g Q).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (show g Q ≤ 1 from prob_le_one)
    have ht3 := ENNReal.toReal_mono (by unfold endpointCompletion; finiteness : endpointCompletion ≠ ∞) ht
    change endpointCompletion.toReal ≤ (g Q).toReal at hgl
    norm_num [endpointCompletion] at hgl ht3
    have hd := delta_real F Q
    have hh := h_real F Q
    have h1 := ENNReal.toReal_mono (by finiteness) hb1
    have h2 := ENNReal.toReal_mono (by finiteness) hb2
    have hg4 := ENNReal.toReal_mono (by finiteness : (4 / 9 : ℝ≥0∞) ≠ ∞) hg.2.1
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow] at h1 h2 hg4
    have hp1 := ENNReal.toReal_nonneg (a := normalizedIterate F g 1 Q)
    have hp2 := ENNReal.toReal_nonneg (a := normalizedIterate F g 2 Q)
    have he : 0 ≤ excess Q := by unfold excess; linarith
    have hδ : excess Q / 3 ≤ delta F Q := by unfold excess; linarith
    refine ⟨by linarith, by norm_num at h1 h2; linarith, he, hd, hδ, ?_⟩
    apply (ENNReal.toReal_le_toReal (Th_finite F Q) (h_finite F Q)).mp
    have := le_trans (div_nonneg he (by norm_num : (0 : ℝ) ≤ 3)) hδ
    change 0 ≤ h F Q - (normalizedAction F (threeStepAverage F) Q).toReal at this
    exact sub_nonneg.mp this

theorem h_measurable (F : CommonFlow) : Measurable (threeStepAverage F) := by
  have hm : Measurable (h F) := by
    have hm := (common_flow_signed_h F).1
    rw [descriptor_tv_borel_eq .p] at hm
    exact hm
  convert hm.ennreal_ofReal using 1
  funext Q
  exact (ENNReal.ofReal_toReal (h_finite F Q)).symm

def qIterate (F : CommonFlow) (n : ℕ) : PDescriptor → ℝ≥0∞ :=
  normalizedIterate F (threeStepAverage F) n

def q (F : CommonFlow) (Q : PDescriptor) : ℝ≥0∞ := ⨅ n, qIterate F n Q

private theorem qIterate_measurable (F : CommonFlow) (n : ℕ) : Measurable (qIterate F n) :=
  measurable_normalizedIterate F _ (h_measurable F) n

private theorem qIterate_step (F : CommonFlow) (n : ℕ) (Q : PDescriptor) :
    qIterate F (n + 1) Q = normalizedAction F (qIterate F n) Q :=
  normalizedIterate_succ F _ (h_measurable F) n Q

theorem qIterate_zero (F : CommonFlow) (Q : PDescriptor) :
    qIterate F 0 Q = threeStepAverage F Q := by
  simp [qIterate, normalizedIterate, iterate]

private theorem qIterate_decreases (F : CommonFlow) (n : ℕ) :
    ∀ᵐ Q ∂F.nuP, qIterate F (n + 1) Q ≤ qIterate F n Q := by
  induction n with
  | zero =>
    filter_upwards [(common_flow_signed_h F).2] with Q hQ
    have hz : qIterate F 0 = threeStepAverage F := funext (qIterate_zero F)
    rw [qIterate_step, hz]
    exact hQ.2.2.2.2.2
  | succ n ih =>
    have hc := Measure.ae_ae_of_ae_comp (κ := F.C)
      ((common_flow_word_iteration F).1.symm ▸ ih)
    filter_upwards [hc] with Q hQ
    rw [qIterate_step, qIterate_step]
    exact mul_le_mul_of_nonneg_left
      (lintegral_mono_ae ((L_le_C F Q).absolutelyContinuous.ae_le hQ)) bot_le

private theorem qIterate_antitone (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, Antitone (fun n => qIterate F n Q) := by
  filter_upwards [ae_all_iff.mpr (qIterate_decreases F)] with Q hQ
  exact antitone_nat_of_succ_le hQ

theorem h_global_bound (F : CommonFlow) (R : PDescriptor) :
    threeStepAverage F R ≤ 10 := by
    apply (ENNReal.toReal_le_toReal (h_finite F R) (by norm_num)).mp
    have h0 : (g R).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (show g R ≤ 1 from prob_le_one)
    have h1 := normalized_g_real_bound F 1 R
    have h2 := normalized_g_real_bound F 2 R
    rw [show (threeStepAverage F R).toReal = h F R from rfl, h_real]
    norm_num at h1 h2 ⊢
    linarith
private theorem h_integral_finite (F : CommonFlow) (Q : PDescriptor) :
    (∫⁻ R, threeStepAverage F R ∂F.L Q) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (10 : ℝ≥0∞) ≠ ∞ by norm_num)
  calc
    _ ≤ ∫⁻ R, (10 : ℝ≥0∞) ∂F.L Q := lintegral_mono (h_global_bound F)
    _ ≤ ∫⁻ R, (10 : ℝ≥0∞) ∂F.C Q := lintegral_mono' (L_le_C F Q) (le_refl _)
    _ = 10 := by simp

/-- Decreasing convergence and harmonicity are conclusions on the original stationary margin. -/
theorem common_flow_q_limit (F : CommonFlow) :
    Measurable (q F) ∧
    ∀ᵐ Q ∂F.nuP, Antitone (fun n => qIterate F n Q) ∧
      Tendsto (fun n => qIterate F n Q) atTop (𝓝 (q F Q)) ∧
      q F Q ≤ threeStepAverage F Q ∧
      normalizedAction F (q F) Q = q F Q := by
  refine ⟨Measurable.iInf (qIterate_measurable F), ?_⟩
  have hc := Measure.ae_ae_of_ae_comp (κ := F.C)
    ((common_flow_word_iteration F).1.symm ▸ qIterate_antitone F)
  filter_upwards [qIterate_antitone F, hc] with Q hQ hrow
  refine ⟨hQ, tendsto_atTop_iInf hQ, ?_, ?_⟩
  · exact (iInf_le (fun n => qIterate F n Q) 0).trans_eq (qIterate_zero F Q)
  · have hrow' := (L_le_C F Q).absolutelyContinuous.ae_le hrow
    have hi := lintegral_iInf_ae (qIterate_measurable F)
      (fun n => Filter.Eventually.mono hrow' (fun R hR => hR n.le_succ))
      (by simpa only [qIterate_zero] using h_integral_finite F Q)
    unfold normalizedAction q
    rw [hi, ENNReal.mul_iInf_of_ne
      (ENNReal.inv_ne_zero.mpr (by unfold endpointRate; finiteness))
      (ENNReal.inv_ne_top.mpr (by norm_num [endpointRate]))]
    change (⨅ n, normalizedAction F (qIterate F n) Q) = (⨅ n, qIterate F n Q)
    simp_rw [← qIterate_step]
    apply le_antisymm
    · apply le_iInf
      intro n
      exact (iInf_le (fun k => qIterate F (k + 1) Q) n).trans (hQ n.le_succ)
    · apply le_iInf
      intro n
      exact iInf_le _ _

def sixthFunctional (F : CommonFlow) (Q : PDescriptor) : ℝ≥0∞ :=
  q F Q ^ 6 / threeStepAverage F Q ^ 5

private theorem q_le_h (F : CommonFlow) (Q : PDescriptor) :
    q F Q ≤ threeStepAverage F Q :=
  (iInf_le (fun n => qIterate F n Q) 0).trans_eq (qIterate_zero F Q)

theorem sixth_le_h (F : CommonFlow) (Q : PDescriptor) :
    sixthFunctional F Q ≤ threeStepAverage F Q := by
  by_cases hh : threeStepAverage F Q = 0
  · have hq : q F Q = 0 := bot_unique ((q_le_h F Q).trans_eq hh)
    simp [sixthFunctional, hh, hq]
  · apply (ENNReal.div_le_iff (pow_ne_zero 5 hh) (ENNReal.pow_ne_top (h_finite F Q))).mpr
    calc
      q F Q ^ 6 ≤ threeStepAverage F Q ^ 6 := by gcongr; exact q_le_h F Q
      _ = threeStepAverage F Q * threeStepAverage F Q ^ 5 := by ring

theorem sixth_measurable (F : CommonFlow) : Measurable (sixthFunctional F) :=
  ((common_flow_q_limit F).1.pow_const 6).div ((h_measurable F).pow_const 5)

private theorem sixth_integral_finite (F : CommonFlow) (Q : PDescriptor) :
    (∫⁻ R, sixthFunctional F R ∂F.L Q) ≠ ∞ :=
  ne_top_of_le_ne_top (h_integral_finite F Q) (lintegral_mono (sixth_le_h F))

private theorem sixth_factorization (F : CommonFlow) (Q : PDescriptor)
    (hh : threeStepAverage F Q ≠ 0) :
    sixthFunctional F Q ^ (1 / 6 : ℝ) * threeStepAverage F Q ^ (5 / 6 : ℝ) = q F Q := by
  have hq6 : (q F Q ^ 6) ^ (1 / 6 : ℝ) = q F Q := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hh5 : (threeStepAverage F Q ^ 5) ^ (1 / 6 : ℝ) =
      threeStepAverage F Q ^ (5 / 6 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold sixthFunctional
  rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), hq6, hh5]
  apply ENNReal.div_mul_cancel
  · exact (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num)).not.mpr hh
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (h_finite F Q)

private theorem sixth_moment (F : CommonFlow) (Q : PDescriptor)
    (hrow : ∀ᵐ R ∂F.L Q, threeStepAverage F R ≠ 0)
    (hq : normalizedAction F (q F) Q = q F Q) :
    q F Q ^ 6 ≤ normalizedAction F (sixthFunctional F) Q *
      normalizedAction F (threeStepAverage F) Q ^ 5 := by
  let μ := endpointRate⁻¹ • F.L Q
  have hp := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ) (f := sixthFunctional F) (g := threeStepAverage F)
    (sixth_measurable F).aemeasurable (h_measurable F).aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 6) (by norm_num : (0 : ℝ) ≤ 5 / 6)
    (by norm_num : (1 / 6 : ℝ) + 5 / 6 = 1)
  have he : (∫⁻ R, sixthFunctional F R ^ (1 / 6 : ℝ) *
      threeStepAverage F R ^ (5 / 6 : ℝ) ∂μ) = ∫⁻ R, q F R ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_smul_measure hrow endpointRate⁻¹] with R hR
    exact sixth_factorization F R hR
  rw [he] at hp
  have hp6 := ENNReal.rpow_le_rpow hp (by norm_num : (0 : ℝ) ≤ 6)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hp6
  simp only [← ENNReal.rpow_mul] at hp6
  norm_num at hp6
  have hm (f : PDescriptor → ℝ≥0∞) : (∫⁻ R, f R ∂μ) = normalizedAction F f Q := by
    simp only [μ, normalizedAction, lintegral_smul_measure, smul_eq_mul]
  rw [hm, hm, hm, hq] at hp6
  exact hp6

private theorem sixth_gain_scalar (x y z e : ℝ) (hx : 0 ≤ x) (hy : 0 < y)
    (hz : 0 ≤ z) (he : 0 ≤ e) (hy2 : y ≤ 1 / 2) (hδ : e / 3 ≤ y - z)
    (a : ℝ) (ha : a ≤ x * z ^ 5) :
    a / y ^ 5 * (1 + 10 * e / 3) ≤ x := by
  have hp : z ^ 5 * (y + 5 * (y - z)) ≤ y ^ 6 := by
    have hn : 0 ≤ (y - z) ^ 2 * (y ^ 4 + 2*y^3*z + 3*y^2*z^2 + 4*y*z^3 + 5*z^4) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith only [hn]
  have hg : y * (1 + 10 * e / 3) ≤ y + 5 * (y - z) := by
    nlinarith
  have hb : z ^ 5 * (1 + 10 * e / 3) ≤ y ^ 5 := by
    apply (mul_le_mul_iff_right₀ hy).mp
    calc
      y * (z ^ 5 * (1 + 10 * e / 3)) = z ^ 5 * (y * (1 + 10 * e / 3)) := by ring
      _ ≤ z ^ 5 * (y + 5 * (y - z)) := mul_le_mul_of_nonneg_left hg (pow_nonneg hz _)
      _ ≤ y ^ 6 := hp
      _ = y * y ^ 5 := by ring
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hy 5)).mpr
  calc
    a * (1 + 10 * e / 3) ≤ (x * z ^ 5) * (1 + 10 * e / 3) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    _ = x * (z ^ 5 * (1 + 10 * e / 3)) := by ring
    _ ≤ x * y ^ 5 := mul_le_mul_of_nonneg_left hb hx

/-- Weighted Holder and the signed defect give the sixth-power gain on the same flow. -/
theorem common_flow_sixth_power_gain (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, sixthFunctional F Q * ENNReal.ofReal (1 + 10 * excess Q / 3) ≤
      normalizedAction F (sixthFunctional F) Q := by
  have hn : ∀ᵐ R ∂F.nuP, threeStepAverage F R ≠ 0 :=
    (common_flow_signed_h F).2.mono (fun R hR => by
      have hp : 0 < h F R := lt_of_lt_of_le (by norm_num) hR.1
      exact ne_of_gt (ENNReal.toReal_pos_iff.mp hp).1)
  have hc := Measure.ae_ae_of_ae_comp (κ := F.C) ((common_flow_word_iteration F).1.symm ▸ hn)
  filter_upwards [(common_flow_signed_h F).2, (common_flow_q_limit F).2, hc] with Q hh hq hrow
  have hm := sixth_moment F Q ((L_le_C F Q).absolutelyContinuous.ae_le hrow) hq.2.2.2
  have hf : normalizedAction F (sixthFunctional F) Q ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by norm_num [endpointRate]))
      (sixth_integral_finite F Q)
  have hmr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf (ENNReal.pow_ne_top (Th_finite F Q))) hm
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at hmr
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q))
      ENNReal.ofReal_ne_top) hf).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hh.2.2.1] :
    0 ≤ 1 + 10 * excess Q / 3)]
  simp only [sixthFunctional, ENNReal.toReal_div, ENNReal.toReal_pow]
  apply sixth_gain_scalar _ _ _ _ ENNReal.toReal_nonneg
    (lt_of_lt_of_le (by norm_num) hh.1) ENNReal.toReal_nonneg hh.2.2.1 hh.2.1
    (by simpa only [delta] using hh.2.2.2.2.1) _ hmr

theorem completion_distortion (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, endpointRate⁻¹ • F.L Q ≤
      ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q := by
  filter_upwards [(common_flow_word_iteration F).2.2] with Q hg
  have hcomp : (1 - u Q) * (3 / 5 : ℝ≥0∞) ≤ g Q := by
    rw [hg]
    apply mul_le_mul' le_rfl
    calc
      (3 / 5 : ℝ≥0∞) = ∫⁻ _ : BDescriptor, (1 - NativeBorelCommonFlow.upper) ∂F.B Q := by
        simp [one_sub_upper]
      _ ≤ _ := lintegral_mono (fun W => tsub_le_tsub_left W.property.2.1 1)
  have hcoef : endpointRate⁻¹ * ((1 - u Q) * NativeBorelCommonFlow.upper) ≤
      ENNReal.ofReal (1 + 25 * excess Q / 9) := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by norm_num [endpointRate]))
        (ENNReal.mul_ne_top (ENNReal.sub_ne_top (by simp))
          (by unfold NativeBorelCommonFlow.upper; finiteness))) ENNReal.ofReal_ne_top).mp
    have hc := ENNReal.toReal_mono (measure_ne_top (law Q) _) hcomp
    have hu : u Q ≤ 1 := prob_le_one
    rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hu (by simp)] at hc
    have hg0 : 0 ≤ (g Q).toReal := ENNReal.toReal_nonneg
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hu (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (by unfold excess; linarith)]
    norm_num [endpointRate, NativeBorelCommonFlow.upper] at hc ⊢
    change (1 - (u Q).toReal) * (3 / 5) ≤ (g Q).toReal at hc
    unfold excess
    linarith
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    L_apply _ _ _ hs]
  have hi : (∫⁻ W, v W * F.A W s ∂F.B Q) ≤ NativeBorelCommonFlow.upper * F.C Q s := by
    rw [CommonFlow.C, Kernel.comp_apply' _ _ _ hs,
      ← lintegral_const_mul _ (F.A.measurable_coe hs)]
    exact lintegral_mono (fun W => mul_le_mul' W.property.2.1 le_rfl)
  calc
    _ ≤ endpointRate⁻¹ * ((1 - u Q) * (NativeBorelCommonFlow.upper * F.C Q s)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hi)
    _ = (endpointRate⁻¹ * ((1 - u Q) * NativeBorelCommonFlow.upper)) * F.C Q s := by ring
    _ ≤ _ := mul_le_mul' hcoef le_rfl

private theorem sixth_C_finite (F : CommonFlow) (Q : PDescriptor) :
    (∫⁻ R, sixthFunctional F R ∂F.C Q) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (10 : ℝ≥0∞) ≠ ∞ by norm_num)
  calc
    _ ≤ ∫⁻ _ : PDescriptor, (10 : ℝ≥0∞) ∂F.C Q :=
      lintegral_mono (fun R => (sixth_le_h F R).trans (h_global_bound F R))
    _ = 10 := by simp

/-- The same completion coordinate controls distortion and the unweighted gain. -/
theorem common_flow_unweighted_gain (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP,
      endpointRate⁻¹ • F.L Q ≤ ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q ∧
      sixthFunctional F Q + (9 / 20 : ℝ≥0∞) * ENNReal.ofReal (excess Q) *
        sixthFunctional F Q ≤ ∫⁻ R, sixthFunctional F R ∂F.C Q := by
  filter_upwards [completion_distortion F, common_flow_sixth_power_gain F,
    (common_flow_signed_h F).2, (common_flow_operator_bounds F).2] with Q hd ht hh hg
  refine ⟨hd, ?_⟩
  have hc : normalizedAction F (sixthFunctional F) Q ≤
      ENNReal.ofReal (1 + 25 * excess Q / 9) *
        ∫⁻ R, sixthFunctional F R ∂F.C Q := by
    calc
      _ = ∫⁻ R, sixthFunctional F R ∂endpointRate⁻¹ • F.L Q := by
        simp [normalizedAction, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ R, sixthFunctional F R ∂ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q :=
        lintegral_mono' hd le_rfl
      _ = _ := by simp [lintegral_smul_measure, smul_eq_mul]
  have htr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (sixth_C_finite F Q)) (ht.trans hc)
  have he : excess Q ≤ (19 / 225 : ℝ) := by
    have hb := ENNReal.toReal_mono (by finiteness : (4 / 9 : ℝ≥0∞) ≠ ∞) hg.2.1
    norm_num at hb
    unfold excess
    linarith
  have he0 := hh.2.2.1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + 10 * excess Q / 3),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + 25 * excess Q / 9)] at htr
  apply (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q),
      by apply ENNReal.mul_ne_top; finiteness;
         exact ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q)⟩)
    (sixth_C_finite F Q)).mp
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q))
    (by apply ENNReal.mul_ne_top; finiteness;
        exact ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal he0]
  norm_num
  have hp : (1 + 9 * excess Q / 20) * (1 + 25 * excess Q / 9) ≤
      1 + 10 * excess Q / 3 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hp
    (ENNReal.toReal_nonneg (a := sixthFunctional F Q))
  have hr : 0 < 1 + 25 * excess Q / 9 := by positivity
  nlinarith

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSuperharmonic
