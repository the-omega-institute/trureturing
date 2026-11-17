/- GID: D5/S3/Weil/Mertens/WeightedTailInverse
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/WeightedTailInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive logarithmic weighted-tail inversion for arbitrary real L1 kernels. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

import D5.S3.Weil.Mertens.WeightedTailTransport

namespace D5.S3.Weil.Mertens.WeightedTailInverse

open Real Set MeasureTheory
open scoped Topology
open D5.S3.Weil.Mertens.WeightedTailTransport

noncomputable section

/-- Reciprocal of the actual public logarithmic weight on `(1, ∞)`. -/
def a (t : ℝ) : ℝ := log t ^ 2 / (1 + log t)

/-- The positive derivative of `a`; its integral on a half-line is infinite. -/
def v (t : ℝ) : ℝ := log t * (log t + 2) / (t * (1 + log t) ^ 2)

private lemma a_pos {t : ℝ} (ht : 1 < t) : 0 < a t := by
  have hl : 0 < log t := log_pos ht
  unfold a
  positivity

private lemma v_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ v t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl : 0 < log t := log_pos ht
  unfold v
  positivity

private lemma v_le_inv {t : ℝ} (ht : 1 < t) : v t ≤ 1 / t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl : 0 < log t := log_pos ht
  have hd : 0 < 1 + log t := by linarith
  have hratio : log t * (log t + 2) / (1 + log t) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hd)).mpr
    nlinarith
  calc
    v t = (log t * (log t + 2) / (1 + log t) ^ 2) / t := by
      unfold v
      field_simp [ht0.ne', hd.ne']
      <;> ring
    _ ≤ 1 / t := div_le_div_of_nonneg_right hratio ht0.le

private lemma a_hasDerivAt {t : ℝ} (ht : 1 < t) : HasDerivAt a (v t) t := by
  have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have hl : 0 < log t := log_pos ht
  have hd : 1 + log t ≠ 0 := ne_of_gt (by linarith)
  have hlog := Real.hasDerivAt_log ht0
  have hquot := (hlog.pow 2).div (hlog.const_add 1) hd
  change HasDerivAt (fun z : ℝ => log z ^ 2 / (1 + log z)) (v t) t
  convert hquot using 1
  dsimp [v]
  field_simp [ht0, hd]
  <;> ring

private lemma v_continuousAt {t : ℝ} (ht : 1 < t) : ContinuousAt v t := by
  have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  have hl : 0 < log t := log_pos ht
  have hd : 1 + log t ≠ 0 := ne_of_gt (by linarith)
  have hc := Real.continuousAt_log ht0
  exact (hc.mul (hc.add_const 2)).div
    (continuousAt_id.mul ((hc.const_add 1).pow 2))
    (mul_ne_zero ht0 (pow_ne_zero 2 hd))

private lemma v_measurable : Measurable v := by
  exact (Real.measurable_log.mul (Real.measurable_log.add_const 2)).div
    (measurable_id.mul ((Real.measurable_log.const_add 1).pow_const 2))

private lemma v_intervalIntegrable {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    IntervalIntegrable v volume x u := by
  apply ContinuousOn.intervalIntegrable_of_Icc hxu
  intro t ht
  exact (v_continuousAt (lt_of_lt_of_le hx ht.1)).continuousWithinAt

private lemma integral_v_interval {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    (∫ t in x..u, v t) = a u - a x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (hint := v_intervalIntegrable hx hxu)
  intro t ht
  rw [uIcc_of_le hxu] at ht
  exact a_hasDerivAt (lt_of_lt_of_le hx ht.1)

private lemma integral_v_Ioo {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    (∫ t in Ioo x u, v t) = a u - a x := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hxu]
  exact integral_v_interval hx hxu

private lemma a_sub_nonneg {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) : 0 ≤ a u - a x := by
  rw [← integral_v_Ioo hx hxu]
  exact setIntegral_nonneg measurableSet_Ioo
    (fun t ht => v_nonneg (lt_trans hx ht.1))

private lemma r_mul_a {t : ℝ} (ht : 1 < t) : r t * a t = 1 := by
  have hl : log t ≠ 0 := (log_pos ht).ne'
  have hd : 1 + log t ≠ 0 := ne_of_gt (by linarith [log_pos ht])
  unfold r a
  field_simp [hl, hd]
  <;> ring

private lemma r_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ r t := by
  have hl : 0 < log t := log_pos ht
  unfold r
  positivity

private lemma normalized_mass {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    0 ≤ r u * (a u - a x) ∧ r u * (a u - a x) ≤ 1 := by
  have hu : 1 < u := lt_of_lt_of_le hx hxu
  constructor
  · exact mul_nonneg (r_nonneg hu) (a_sub_nonneg hx hxu)
  · calc
      r u * (a u - a x) ≤ r u * a u :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (a_pos hx).le) (r_nonneg hu)
      _ = 1 := r_mul_a hu

/- The first variable is truncated before its integral is taken. No
   integrability of `v` on a half-line is used anywhere below. -/
private lemma truncated_v_integrable {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    Integrable ((Iio u).indicator v) (volume.restrict (Ioi x)) := by
  have hi : IntegrableOn v (Ioo x u) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hxu).mp (v_intervalIntegrable hx hxu)
  apply (integrable_indicator_iff measurableSet_Iio).mpr
  change Integrable v ((volume.restrict (Ioi x)).restrict (Iio u))
  rw [Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio u ∩ Ioi x = Ioo x u := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  rw [hs]
  exact hi

private lemma integral_truncated_v {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    (∫ t in Ioi x, (Iio u).indicator v t) = a u - a x := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio u ∩ Ioi x = Ioo x u := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  rw [hs]
  exact integral_v_Ioo hx hxu

private def inverseTriangle (k : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then v p.1 * (k p.2 * r p.2) else 0

private lemma triangle_as_truncation (k : ℝ → ℝ) (u : ℝ) :
    (fun t => inverseTriangle k (t, u)) =
      (fun t => (Iio u).indicator v t * (k u * r u)) := by
  funext t
  by_cases h : t < u <;> simp [inverseTriangle, indicator_apply, h]

private lemma triangle_inner {k : ℝ → ℝ} {x u : ℝ} (hx : 1 < x) (hxu : x ≤ u) :
    (∫ t in Ioi x, inverseTriangle k (t, u)) =
      (k u * r u) * (a u - a x) := by
  rw [triangle_as_truncation, integral_mul_const, integral_truncated_v hx hxu]
  ring

private lemma triangle_norm_inner {k : ℝ → ℝ} {x u : ℝ} (hx : 1 < x)
    (hxu : x ≤ u) :
    (∫ t in Ioi x, ‖inverseTriangle k (t, u)‖) =
      |k u| * (r u * (a u - a x)) := by
  have hu : 1 < u := lt_of_lt_of_le hx hxu
  calc
    (∫ t in Ioi x, ‖inverseTriangle k (t, u)‖) =
        ∫ t in Ioi x, (Iio u).indicator v t * (|k u| * r u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht1 : 1 < t := lt_trans hx ht
      by_cases htu : t < u
      · simp only [inverseTriangle, if_pos htu, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (v_nonneg ht1), abs_of_nonneg (r_nonneg hu),
          indicator_of_mem (show t ∈ Iio u from htu)]
      · simp [inverseTriangle, htu, indicator_apply]
    _ = |k u| * (r u * (a u - a x)) := by
      rw [integral_mul_const, integral_truncated_v hx hxu]
      ring

private lemma triangle_section {k : ℝ → ℝ} {x t : ℝ} (hxt : x < t) :
    (∫ u in Ioi x, inverseTriangle k (t, u)) = v t * weightedTail k t := by
  have heq : (fun u => inverseTriangle k (t, u)) =
      (fun u => v t * (Ioi t).indicator (fun s => k s * r s) u) := by
    funext u
    by_cases h : t < u <;> simp [inverseTriangle, indicator_apply, h]
  rw [heq, integral_const_mul, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hxt.le)]
  <;> rfl

/- Absolute Fubini is proved using `integrable_prod_iff'`, with the inner
   first-variable norm integral bounded by `|k u|`. -/
private lemma inverseTriangle_integrable {k : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hk : IntegrableOn k (Ioi x)) :
    Integrable (inverseTriangle k)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) := by
  have hx1 : 1 < x := by linarith
  have hkr := (WeightedTailTransport.transport hx hk).1
  have hm : AEStronglyMeasurable (inverseTriangle k)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) := by
    have hv : AEStronglyMeasurable v (volume.restrict (Ioi x)) :=
      v_measurable.aestronglyMeasurable
    have hp : AEStronglyMeasurable (fun p : ℝ × ℝ => v p.1 * (k p.2 * r p.2))
        ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) :=
      hv.comp_fst.mul hkr.aestronglyMeasurable.comp_snd
    have he : inverseTriangle k = {p : ℝ × ℝ | p.1 < p.2}.indicator
        (fun p => v p.1 * (k p.2 * r p.2)) := by
      funext p
      rfl
    rw [he]
    exact hp.indicator (measurableSet_lt measurable_fst measurable_snd)
  apply (integrable_prod_iff' hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [triangle_as_truncation]
    exact (truncated_v_integrable hx1 hu.le).mul_const (k u * r u)
  · have hn : AEStronglyMeasurable
        (fun u => ∫ t in Ioi x, ‖inverseTriangle k (t, u)‖)
        (volume.restrict (Ioi x)) := hm.prod_swap.norm.integral_prod_right'
    apply hk.abs.mono' hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hnonneg : 0 ≤ ∫ t in Ioi x, ‖inverseTriangle k (t, u)‖ :=
      integral_nonneg (fun t => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, triangle_norm_inner hx1 hu.le]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (normalized_mass hx1 hu.le).2 (abs_nonneg (k u))

/-- Invert the actual logarithmic tail weight for an arbitrary real L1 kernel.
There is no boundary hypothesis and no logarithmically weighted moment premise. -/
theorem inverse {k : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hk : IntegrableOn k (Ioi x)) :
    IntegrableOn (fun t => v t * weightedTail k t) (Ioi x) ∧
      tail k x = a x * weightedTail k x +
        ∫ t in Ioi x, v t * weightedTail k t := by
  have hx1 : 1 < x := by linarith
  have hkr := (WeightedTailTransport.transport hx hk).1
  have hf := inverseTriangle_integrable hx hk
  have hj : IntegrableOn (fun t => v t * weightedTail k t) (Ioi x) := by
    apply hf.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact triangle_section ht
  refine ⟨hj, ?_⟩
  have hswap := integral_integral_swap
    (f := fun t u => inverseTriangle k (t, u)) hf
  have houter : (∫ t in Ioi x, v t * weightedTail k t) =
      ∫ u in Ioi x, k u - a x * (k u * r u) := by
    calc
      (∫ t in Ioi x, v t * weightedTail k t) =
          ∫ t in Ioi x, ∫ u in Ioi x, inverseTriangle k (t, u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact (triangle_section ht).symm
      _ = ∫ u in Ioi x, ∫ t in Ioi x, inverseTriangle k (t, u) := hswap
      _ = ∫ u in Ioi x, k u - a x * (k u * r u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change (∫ t in Ioi x, inverseTriangle k (t, u)) = k u - a x * (k u * r u)
        rw [triangle_inner hx1 hu.le]
        calc
          (k u * r u) * (a u - a x) =
              k u * (r u * a u) - a x * (k u * r u) := by ring
          _ = k u - a x * (k u * r u) := by
            rw [r_mul_a (lt_trans hx1 hu), mul_one]
  rw [integral_sub hk (hkr.const_mul (a x)), integral_const_mul] at houter
  change (∫ t in Ioi x, v t * weightedTail k t) =
    tail k x - a x * weightedTail k x at houter
  linarith only [houter]

private lemma log_ge_one {t : ℝ} (ht : exp 1 ≤ t) : 1 ≤ log t := by
  simpa only [log_exp] using log_le_log (exp_pos 1) ht

private lemma reciprocal_sqrt_eq_rpow {t : ℝ} (ht : 0 < t) :
    (1 / t) / sqrt t = t ^ (-(3 / 2 : ℝ)) := by
  calc
    (1 / t) / sqrt t = t ^ (-1 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
      simp only [div_eq_mul_inv, one_mul, sqrt_eq_rpow, rpow_neg ht.le, rpow_one]
    _ = t ^ ((-1 : ℝ) + -(1 / 2 : ℝ)) := (rpow_add ht _ _).symm
    _ = t ^ (-(3 / 2 : ℝ)) := by norm_num

private lemma v_div_sqrt_log_le {t : ℝ} (ht : exp 1 ≤ t) :
    v t / (sqrt t * log t) ≤ t ^ (-(3 / 2 : ℝ)) := by
  have ht1 : 1 < t := lt_of_lt_of_le (one_lt_exp_iff.mpr (by norm_num)) ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  have hl : 1 ≤ log t := log_ge_one ht
  have hs : 0 < sqrt t := sqrt_pos.2 ht0
  calc
    v t / (sqrt t * log t) ≤ (1 / t) / (sqrt t * log t) :=
      div_le_div_of_nonneg_right (v_le_inv ht1) (by positivity)
    _ ≤ (1 / t) / sqrt t :=
      div_le_div_of_nonneg_left (by positivity) hs (by nlinarith)
    _ = t ^ (-(3 / 2 : ℝ)) := reciprocal_sqrt_eq_rpow ht0

private lemma integral_rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi x, t ^ (-(3 / 2 : ℝ))) = 2 / sqrt x := by
  calc
    (∫ t in Ioi x, t ^ (-(3 / 2 : ℝ))) =
        -x ^ (-(3 / 2 : ℝ) + 1) / (-(3 / 2 : ℝ) + 1) :=
      integral_Ioi_rpow_of_lt (by norm_num) hx
    _ = 2 * x ^ (-(1 / 2 : ℝ)) := by norm_num <;> ring
    _ = 2 / sqrt x := by
      rw [rpow_neg hx.le, ← sqrt_eq_rpow]
      <;> rfl

/-- Consume `inverse` to transfer a one-sided bound on the actual weighted
tail. The input is required on the closed tail, including the endpoint `x`. -/
theorem tail_lower_bound {k : ℝ → ℝ} {x A : ℝ} (hx : exp 1 ≤ x) (hA : 0 ≤ A)
    (hk : IntegrableOn k (Ioi x))
    (hJ : ∀ t ≥ x, weightedTail k t ≥ -A / (sqrt t * log t)) :
    tail k x ≥ -3 * A / sqrt x := by
  have he2 : (2 : ℝ) ≤ exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hx2 : 2 ≤ x := he2.trans hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos hx1
  have hs : 0 < sqrt x := sqrt_pos.2 hx0
  have hinverse := inverse hx2 hk
  have hp : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx0
  have hpoint : ∀ t ∈ Ioi x,
      (-A) * t ^ (-(3 / 2 : ℝ)) ≤ v t * weightedTail k t := by
    intro t ht
    have htE : exp 1 ≤ t := hx.trans ht.le
    have ht1 : 1 < t := lt_trans hx1 ht
    calc
      (-A) * t ^ (-(3 / 2 : ℝ)) ≤ (-A) * (v t / (sqrt t * log t)) :=
        mul_le_mul_of_nonpos_left (v_div_sqrt_log_le htE) (neg_nonpos.mpr hA)
      _ = v t * (-A / (sqrt t * log t)) := by ring
      _ ≤ v t * weightedTail k t :=
        mul_le_mul_of_nonneg_left (hJ t ht.le) (v_nonneg ht1)
  have hint : (-A) * (2 / sqrt x) ≤ ∫ t in Ioi x, v t * weightedTail k t := by
    calc
      (-A) * (2 / sqrt x) = ∫ t in Ioi x, (-A) * t ^ (-(3 / 2 : ℝ)) := by
        rw [integral_const_mul, integral_rpow_neg_three_halves hx0]
      _ ≤ ∫ t in Ioi x, v t * weightedTail k t :=
        setIntegral_mono_on (hp.const_mul (-A)) hinverse.1 measurableSet_Ioi hpoint
  have hratio : a x / log x ≤ 1 := by
    have hd : 0 < 1 + log x := by linarith
    calc
      a x / log x = log x / (1 + log x) := by
        unfold a
        field_simp [hl.ne', hd.ne']
        <;> ring
      _ ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hend : -A / sqrt x ≤ a x * weightedTail k x := by
    calc
      -A / sqrt x = (-A / sqrt x) * 1 := by ring
      _ ≤ (-A / sqrt x) * (a x / log x) :=
        mul_le_mul_of_nonpos_left hratio
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) hs.le)
      _ = a x * (-A / (sqrt x * log x)) := by
        field_simp [hs.ne', hl.ne']
        <;> ring
      _ ≤ a x * weightedTail k x :=
        mul_le_mul_of_nonneg_left (hJ x le_rfl) (a_pos hx1).le
  calc
    -3 * A / sqrt x = -A / sqrt x + (-A) * (2 / sqrt x) := by ring
    _ ≤ a x * weightedTail k x + ∫ t in Ioi x, v t * weightedTail k t :=
      add_le_add hend hint
    _ = tail k x := hinverse.2.symm

#print axioms inverse
#print axioms tail_lower_bound

end
end D5.S3.Weil.Mertens.WeightedTailInverse
