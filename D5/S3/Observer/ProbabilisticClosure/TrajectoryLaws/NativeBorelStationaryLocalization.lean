/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stationarity forces zero completion excess wherever the normalized harmonic limit survives. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSuperharmonic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStationaryLocalization
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open NativeBorelCommonFlow NativeBorelSuperharmonic

/-- The invariant margin settles the nonnegative gain; localization is earned. -/
theorem common_flow_stationary_localization (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP,
      (∫⁻ R, sixthFunctional F R ∂F.C Q) = sixthFunctional F Q ∧
      ENNReal.ofReal (excess Q) * sixthFunctional F Q = 0 ∧
      (q F Q ≠ 0 → excess Q = 0) := by
  have hm := sixth_measurable F
  have hb (Q : PDescriptor) : sixthFunctional F Q ≤ 10 :=
    (sixth_le_h F Q).trans (h_global_bound F Q)
  have hi : (∫⁻ Q, sixthFunctional F Q ∂F.nuP) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show (10 : ℝ≥0∞) ≠ ∞ by norm_num)
    calc
      _ ≤ ∫⁻ _ : PDescriptor, (10 : ℝ≥0∞) ∂F.nuP := lintegral_mono hb
      _ = 10 := by simp
  have hs := (common_flow_word_iteration F).1
  change F.nuP.bind F.C = F.nuP at hs
  have heq : (∫⁻ Q, ∫⁻ R, sixthFunctional F R ∂F.C Q ∂F.nuP) =
      ∫⁻ Q, sixthFunctional F Q ∂F.nuP := by
    rw [← Measure.lintegral_bind F.C.aemeasurable hm.aemeasurable, hs]
  have hle : ∀ᵐ Q ∂F.nuP, sixthFunctional F Q ≤ ∫⁻ R, sixthFunctional F R ∂F.C Q :=
    (common_flow_unweighted_gain F).mono (fun Q hQ => le_trans le_self_add hQ.2)
  have he := ae_eq_of_ae_le_of_lintegral_le hle hi hm.lintegral_kernel.aemeasurable heq.le
  filter_upwards [he, common_flow_unweighted_gain F, (common_flow_signed_h F).2]
    with Q hQ hgain hh
  have hf : sixthFunctional F Q ≠ ∞ := ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q)
  have hzero : (9 / 20 : ℝ≥0∞) * ENNReal.ofReal (excess Q) * sixthFunctional F Q = 0 := by
    rw [← hQ] at hgain
    exact nonpos_iff_eq_zero.mp ((ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right.mp hgain.2)
  have hz : ENNReal.ofReal (excess Q) * sixthFunctional F Q = 0 := by
    rw [mul_assoc, mul_eq_zero] at hzero
    exact hzero.resolve_left (by norm_num)
  refine ⟨hQ.symm, hz, ?_⟩
  intro hq
  have hfn : sixthFunctional F Q ≠ 0 := by
    intro hf0
    have hdiv := ENNReal.div_eq_zero_iff.mp hf0
    exact hdiv.elim (pow_ne_zero 6 hq) (ENNReal.pow_ne_top (h_finite F Q))
  have he0 : ENNReal.ofReal (excess Q) = 0 := (mul_eq_zero.mp hz).resolve_right hfn
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp he0) hh.2.2.1

private theorem second_moment (F : CommonFlow) (Q : PDescriptor) :
    (∫⁻ R, sixthFunctional F R ∂F.C Q) ^ 2 ≤
      ∫⁻ R, sixthFunctional F R ^ 2 ∂F.C Q := by
  have hp := ENNReal.lintegral_mul_norm_pow_le (μ := F.C Q)
    (f := fun R => sixthFunctional F R ^ 2) (g := fun _ => 1)
    ((sixth_measurable F).pow_const 2).aemeasurable measurable_const.aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he (R : PDescriptor) : (sixthFunctional F R ^ 2) ^ (1 / 2 : ℝ) =
      sixthFunctional F R := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [ENNReal.one_rpow, mul_one, he, lintegral_one, measure_univ] at hp
  have hs := ENNReal.rpow_le_rpow hp (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at hs
  norm_num at hs
  exact hs

/-- The original stationary acquired edges preserve the sixth functional almost surely. -/
theorem common_flow_stationary_edges (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, ∀ᵐ R ∂F.C Q, sixthFunctional F R = sixthFunctional F Q := by
  have hm := sixth_measurable F
  have hf (Q : PDescriptor) : sixthFunctional F Q ≠ ∞ :=
    ne_top_of_le_ne_top (h_finite F Q) (sixth_le_h F Q)
  have hb (Q : PDescriptor) : sixthFunctional F Q ≤ 10 :=
    (sixth_le_h F Q).trans (h_global_bound F Q)
  have hm2 := hm.pow_const 2
  have hi : (∫⁻ Q, sixthFunctional F Q ^ 2 ∂F.nuP) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show (100 : ℝ≥0∞) ≠ ∞ by norm_num)
    calc
      _ ≤ ∫⁻ _ : PDescriptor, (100 : ℝ≥0∞) ∂F.nuP := by
        apply lintegral_mono
        intro Q
        calc
          _ ≤ (10 : ℝ≥0∞) ^ 2 := pow_le_pow_left' (hb Q) 2
          _ = 100 := by norm_num
      _ = 100 := by simp
  have hs := (common_flow_word_iteration F).1
  change F.nuP.bind F.C = F.nuP at hs
  have heq : (∫⁻ Q, ∫⁻ R, sixthFunctional F R ^ 2 ∂F.C Q ∂F.nuP) =
      ∫⁻ Q, sixthFunctional F Q ^ 2 ∂F.nuP := by
    rw [← Measure.lintegral_bind F.C.aemeasurable hm2.aemeasurable, hs]
  have hle : ∀ᵐ Q ∂F.nuP, sixthFunctional F Q ^ 2 ≤
      ∫⁻ R, sixthFunctional F R ^ 2 ∂F.C Q := by
    filter_upwards [common_flow_stationary_localization F] with Q hQ
    simpa only [hQ.1] using second_moment F Q
  have he := ae_eq_of_ae_le_of_lintegral_le hle hi hm2.lintegral_kernel.aemeasurable heq.le
  filter_upwards [common_flow_stationary_localization F, he] with Q hQ hQ2
  have hmR : Measurable (fun R => (sixthFunctional F R).toReal) := hm.ennreal_toReal
  have hmem : MemLp (fun R => (sixthFunctional F R).toReal) 2 (F.C Q) :=
    memLp_of_bounded (Filter.Eventually.of_forall (fun R =>
      ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by norm_num) (hb R)⟩))
      hmR.aestronglyMeasurable 2
  have hr1 : (∫ R, (sixthFunctional F R).toReal ∂F.C Q) =
      (sixthFunctional F Q).toReal := by
    rw [integral_toReal hm.aemeasurable (Filter.Eventually.of_forall (fun R => (hf R).lt_top)),
      hQ.1]
  have hr2 : (∫ R, (sixthFunctional F R).toReal ^ 2 ∂F.C Q) =
      (sixthFunctional F Q).toReal ^ 2 := by
    have hi2 := integral_toReal (μ := F.C Q) hm2.aemeasurable
      (Filter.Eventually.of_forall (fun R => (ENNReal.pow_ne_top (hf R)).lt_top))
    simpa only [ENNReal.toReal_pow, ← hQ2] using hi2
  have hv : variance (fun R => (sixthFunctional F R).toReal) (F.C Q) = 0 := by
    rw [variance_eq_sub hmem]
    change (∫ R, (sixthFunctional F R).toReal ^ 2 ∂F.C Q) -
      (∫ R, (sixthFunctional F R).toReal ∂F.C Q) ^ 2 = 0
    rw [hr1, hr2, sub_self]
  filter_upwards [ae_eq_integral_of_variance_eq_zero hmem hv] with R hR
  apply (ENNReal.toReal_eq_toReal_iff' (hf R) (hf Q)).mp
  exact hR.trans hr1

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStationaryLocalization
