/- GID: D5/S3/Topology/Measures/BrezisLiebPowerDefect
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/BrezisLiebPowerDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded positive-power mass and a.e. convergence give full L1 power splitting. -/

module

public import D5.S3.Topology.Measures.IntegralEpsilonDomination
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Brézis–Lieb power splitting

On an arbitrary measure space, bounded positive-power mass and almost-everywhere
convergence of complex functions imply convergence of the full absolute defect
in L1, with integrability of every energy and the corresponding signed splitting.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace D5.S3.Topology.Measures.BrezisLiebPowerDefect

universe u

private theorem power_increment_bound (p : ℝ) (hp : 0 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ,
      |‖a + b‖ ^ p - ‖a‖ ^ p| ≤ ε * ‖a‖ ^ p + C * ‖b‖ ^ p := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1
    (Real.continuousAt_rpow_const 1 p (Or.inr hp.le)) ε hε
  let A : ℝ := δ⁻¹
  have hA : 0 ≤ A := inv_nonneg.mpr hδ.le
  refine ⟨(A + 1) ^ p + A ^ p, add_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg hA _), ?_⟩
  intro a b
  by_cases hsmall : ‖b‖ < δ * ‖a‖
  · have ha : 0 < ‖a‖ := by nlinarith [norm_nonneg b]
    have hratio : |‖a + b‖ / ‖a‖ - 1| < δ := by
      rw [div_sub_one ha.ne', abs_div, abs_of_pos ha]
      apply (div_lt_iff₀ ha).2
      have hn : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := by
        simpa using abs_norm_sub_norm_le (a + b) a
      exact hn.trans_lt hsmall
    have hc : |(‖a + b‖ / ‖a‖) ^ p - 1| < ε := by
      simpa only [Real.dist_eq, Real.one_rpow] using hclose hratio
    have heq : |‖a + b‖ ^ p - ‖a‖ ^ p| =
        |(‖a + b‖ / ‖a‖) ^ p - 1| * ‖a‖ ^ p := by
      have hraw : ‖a + b‖ ^ p - ‖a‖ ^ p =
          ((‖a + b‖ / ‖a‖) ^ p - 1) * ‖a‖ ^ p := by
        rw [sub_mul, one_mul, ← Real.mul_rpow (div_nonneg (norm_nonneg _) ha.le) ha.le,
          div_mul_cancel₀ _ ha.ne']
      rw [hraw, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg a) p)]
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hc.le (Real.rpow_nonneg (norm_nonneg a) p)).trans
      (le_add_of_nonneg_right (mul_nonneg
        (add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hA _))
        (Real.rpow_nonneg (norm_nonneg b) p)))
  · have hlarge : δ * ‖a‖ ≤ ‖b‖ := le_of_not_gt hsmall
    have hab : ‖a‖ ≤ A * ‖b‖ := by
      dsimp [A]
      rw [inv_mul_eq_div, le_div_iff₀ hδ]
      nlinarith
    have hsum : ‖a + b‖ ≤ (A + 1) * ‖b‖ :=
      (norm_add_le a b).trans (by nlinarith)
    have hpa := Real.rpow_le_rpow (norm_nonneg a) hab hp.le
    have hps := Real.rpow_le_rpow (norm_nonneg (a + b)) hsum hp.le
    rw [Real.mul_rpow hA (norm_nonneg b)] at hpa
    rw [Real.mul_rpow (by linarith : 0 ≤ A + 1) (norm_nonneg b)] at hps
    calc
      |‖a + b‖ ^ p - ‖a‖ ^ p| ≤ ‖a + b‖ ^ p + ‖a‖ ^ p :=
        abs_sub_le_iff.2 ⟨by linarith [Real.rpow_nonneg (norm_nonneg a) p],
          by linarith [Real.rpow_nonneg (norm_nonneg (a + b)) p]⟩
      _ ≤ ε * ‖a‖ ^ p + ((A + 1) ^ p + A ^ p) * ‖b‖ ^ p := by
        nlinarith [mul_nonneg hε.le (Real.rpow_nonneg (norm_nonneg a) p)]

/-- Full L1 Brézis–Lieb power splitting on an arbitrary measure space. -/
theorem brezis_lieb_power_defect {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 0 < p) (M : ℝ≥0)
    (f : ℕ → Ω → ℂ) (g : Ω → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hM : ∀ n, ∫⁻ x, ‖f n x‖ₑ ^ p ∂μ ≤ (M : ℝ≥0∞)) :
    AEStronglyMeasurable g μ ∧
    (∫⁻ x, ‖g x‖ₑ ^ p ∂μ ≤ (M : ℝ≥0∞)) ∧
    Integrable (fun x => ‖g x‖ ^ p) μ ∧
    (∀ n, Integrable (fun x => ‖f n x‖ ^ p) μ ∧
      Integrable (fun x => ‖f n x - g x‖ ^ p) μ ∧
      Integrable (fun x => ‖f n x‖ ^ p - ‖f n x - g x‖ ^ p - ‖g x‖ ^ p) μ) ∧
    Tendsto (fun n => ∫ x, |‖f n x‖ ^ p - ‖f n x - g x‖ ^ p - ‖g x‖ ^ p| ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n => (∫ x, ‖f n x‖ ^ p ∂μ) - (∫ x, ‖f n x - g x‖ ^ p ∂μ))
      atTop (𝓝 (∫ x, ‖g x‖ ^ p ∂μ)) := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hfg
  have hgmass : ∫⁻ x, ‖g x‖ₑ ^ p ∂μ ≤ (M : ℝ≥0∞) := by
    calc
      _ = ∫⁻ x, liminf (fun n => ‖f n x‖ₑ ^ p) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hfg] with x hx
        exact (hx.enorm.ennrpow_const p).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖f n x‖ₑ ^ p ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hf n).enorm.pow_const p)
      _ ≤ (M : ℝ≥0∞) := liminf_le_of_frequently_le' (Eventually.of_forall hM).frequently
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfp : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ := by
    intro n
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt (hf n)).2
    simpa only [ENNReal.toReal_ofReal hp.le] using (hM n).trans_lt ENNReal.coe_lt_top
  have hgp : MemLp g (ENNReal.ofReal p) μ := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt hg).2
    simpa only [ENNReal.toReal_ofReal hp.le] using hgmass.trans_lt ENNReal.coe_lt_top
  have hgi : Integrable (fun x => ‖g x‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hgp.integrable_norm_rpow hp0 hpt
  have hfi : ∀ n, Integrable (fun x => ‖f n x‖ ^ p) μ := by
    intro n
    simpa only [ENNReal.toReal_ofReal hp.le] using (hfp n).integrable_norm_rpow hp0 hpt
  have hri : ∀ n, Integrable (fun x => ‖f n x - g x‖ ^ p) μ := by
    intro n
    simpa only [ENNReal.toReal_ofReal hp.le, Pi.sub_apply] using
      ((hfp n).sub hgp).integrable_norm_rpow hp0 hpt
  let d : ℕ → Ω → ℝ := fun n x => ‖f n x‖ ^ p - ‖f n x - g x‖ ^ p - ‖g x‖ ^ p
  have hdi : ∀ n, Integrable (d n) μ := fun n => ((hfi n).sub (hri n)).sub hgi
  have hdlim : ∀ᵐ x ∂μ, Tendsto (fun n => d n x) atTop (𝓝 0) := by
    filter_upwards [hfg] with x hx
    have h₁ := hx.norm.rpow_const (Or.inr hp.le)
    have h₂ := (hx.sub_const (g x)).norm.rpow_const (Or.inr hp.le)
    simpa only [d, sub_self, norm_zero, Real.zero_rpow hp.ne', sub_zero] using
      (h₁.sub h₂).sub_const (‖g x‖ ^ p)
  have henergy : ∀ n, ∫ x, ‖f n x‖ ^ p ∂μ ≤ (M : ℝ) := by
    intro n
    have heq : ENNReal.ofReal (∫ x, ‖f n x‖ ^ p ∂μ) = ∫⁻ x, ‖f n x‖ₑ ^ p ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal (hfi n)]
      · congr 1
        funext x
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]
      · exact ae_of_all μ (fun x => Real.rpow_nonneg (norm_nonneg _) _)
    have hb := hM n
    rw [← heq, ← ENNReal.ofReal_coe_nnreal] at hb
    exact (ENNReal.ofReal_le_ofReal_iff M.coe_nonneg).1 hb
  have habs : Tendsto (fun n => ∫ x, |d n x| ∂μ) atTop (𝓝 0) := by
    refine IntegralEpsilonDomination.tendsto_integral_of_epsilon_domination μ
      (fun n x => |d n x|) (M : ℝ) (fun n => (hdi n).abs) ?_
      (fun n x => abs_nonneg _) M.coe_nonneg ?_
    · filter_upwards [hdlim] with x hx
      simpa only [abs_zero] using hx.abs
    · intro ε hε
      obtain ⟨C, hC, hbound⟩ := power_increment_bound p hp ε hε
      refine ⟨(fun n x => ‖f n x‖ ^ p), (fun x => (C + 1) * ‖g x‖ ^ p),
        hfi, hgi.const_mul (C + 1), (fun n x => Real.rpow_nonneg (norm_nonneg _) _),
        (fun x => mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)),
        henergy, ?_⟩
      intro n x
      have hb := hbound (f n x) (-g x)
      simp only [← sub_eq_add_neg, norm_neg] at hb
      have ht := abs_sub (‖f n x‖ ^ p - ‖f n x - g x‖ ^ p) (‖g x‖ ^ p)
      rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at ht
      rw [abs_sub_comm] at hb
      dsimp [d]
      linarith
  refine ⟨hg, hgmass, hgi, fun n => ⟨hfi n, hri n, hdi n⟩, habs, ?_⟩
  have hsigned : Tendsto (fun n => ∫ x, d n x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) habs
    exact norm_integral_le_integral_norm (d n)
  have ht := hsigned.add_const (∫ x, ‖g x‖ ^ p ∂μ)
  have heq (n : ℕ) : (∫ x, d n x ∂μ) =
      (∫ x, ‖f n x‖ ^ p ∂μ) - (∫ x, ‖f n x - g x‖ ^ p ∂μ) -
        (∫ x, ‖g x‖ ^ p ∂μ) := by
    dsimp only [d]
    simpa only [Pi.sub_apply, integral_sub (hfi n) (hri n)] using
      integral_sub ((hfi n).sub (hri n)) hgi
  simp_rw [heq, sub_add_cancel] at ht
  simpa only [zero_add] using ht

#print axioms power_increment_bound
#print axioms brezis_lieb_power_defect

end D5.S3.Topology.Measures.BrezisLiebPowerDefect
