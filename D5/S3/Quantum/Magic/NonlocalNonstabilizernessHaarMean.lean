/- GID: D5/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/NonlocalNonstabilizernessHaarMean
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Haar mean of two-qubit non-local nonstabilizerness is 10/3 minus pi. -/

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set MeasureTheory Filter
open scoped Interval Topology

namespace D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean

/-- z ≡ √(4 − 3e^y) of Appendix C. -/
noncomputable def zC (y : ℝ) : ℝ := Real.sqrt (4 - 3 * Real.exp y)
/-- The density (C5) of y = NN for Haar-random two-qubit states,
on its support 0 < y < ln(4/3), and 0 elsewhere. -/
noncomputable def nnDensity (y : ℝ) : ℝ :=
  if 0 < y ∧ y < Real.log (4 / 3) then
    3 * Real.exp (-y / 2) / (4 * zC y * Real.sqrt (2 * (Real.exp y - 1))) *
      ((Real.exp (y / 2) + zC y) * Real.sqrt (1 - Real.exp (-y / 2) * zC y) +
        (Real.exp (y / 2) - zC y) * Real.sqrt (1 + Real.exp (-y / 2) * zC y))
  else 0
def claim : Prop :=
  MeasureTheory.Integrable (fun y : ℝ => y * nnDensity y) ∧
    ∫ y : ℝ, y * nnDensity y = 10 / 3 - Real.pi

private noncomputable def q (t : ℝ) : ℝ := t ^ 4 - t ^ 2 + 1
private theorem q_eq (t : ℝ) : q t = t ^ 4 - t ^ 2 + 1 := rfl
private theorem q_pos (t : ℝ) : 0 < q t := by
  rw [q_eq]
  nlinarith [sq_nonneg (t ^ 2 - 1 / 2)]

private noncomputable def F (t : ℝ) : ℝ :=
  -t ^ 3 * Real.log (q t) + (4 / 3) * t ^ 3 + 2 * t -
    2 * (Real.arctan (2 * t + Real.sqrt 3) + Real.arctan (2 * t - Real.sqrt 3))
private theorem F_eq (t : ℝ) : F t =
    -t ^ 3 * Real.log (q t) + (4 / 3) * t ^ 3 + 2 * t -
      2 * (Real.arctan (2 * t + Real.sqrt 3) + Real.arctan (2 * t - Real.sqrt 3)) := rfl

private theorem F_deriv (t : ℝ) : HasDerivAt F (-3 * t ^ 2 * Real.log (q t)) t := by
  have hq : HasDerivAt q (4 * t ^ 3 - 2 * t) t := by
    convert (((hasDerivAt_id t).pow 4).sub ((hasDerivAt_id t).pow 2)).add_const 1
      using 1 <;> try rfl
    simp only [id_eq]
    norm_num
  have hlog := hq.log (q_pos t).ne'
  have hp := ((hasDerivAt_id t).const_mul 2).add_const (Real.sqrt 3)
  have hm := ((hasDerivAt_id t).const_mul 2).sub_const (Real.sqrt 3)
  have h := ((((hasDerivAt_id t).pow 3).neg.mul hlog).add
    (((hasDerivAt_id t).pow 3).const_mul (4 / 3))).add
    ((hasDerivAt_id t).const_mul 2) |>.sub ((hp.arctan.add hm.arctan).const_mul 2)
  simp only [id_eq, Pi.pow_apply, Pi.neg_apply] at h
  convert h using 1 <;> try rfl
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd1 : 1 + (2 * t + Real.sqrt 3) ^ 2 ≠ 0 := by positivity
  have hd2 : 1 + (2 * t - Real.sqrt 3) ^ 2 ≠ 0 := by positivity
  have hqn := (q_pos t).ne'
  field_simp [hqn, hd1, hd2]
  simp only [q_eq]
  ring_nf
  have hs4 : Real.sqrt 3 ^ 4 = 9 := by nlinarith [sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
  simp only [hs, hs4]
  ring

private theorem F_zero : F 0 = 0 := by
  rw [F_eq, q_eq]
  norm_num [Real.arctan_neg]

private theorem F_one : F 1 = 10 / 3 - Real.pi := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hp : 0 < 2 + Real.sqrt 3 := by positivity
  have hrec : 2 - Real.sqrt 3 = (2 + Real.sqrt 3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    nlinarith
  have ha : Real.arctan (2 + Real.sqrt 3) + Real.arctan (2 - Real.sqrt 3) =
      Real.pi / 2 := by
    rw [hrec, Real.arctan_inv_of_pos hp]
    ring
  rw [F_eq, q_eq]
  norm_num only [one_pow, sub_self, zero_add, Real.log_one, mul_one, neg_mul,
    mul_zero, zero_add]
  rw [ha]
  ring

private theorem a_pos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)

private noncomputable def w (y : ℝ) : ℝ := Real.sqrt (4 * Real.exp (-y) - 3)
private theorem w_eq (y : ℝ) : w y = Real.sqrt (4 * Real.exp (-y) - 3) := rfl
private noncomputable def tm (y : ℝ) : ℝ := Real.sqrt ((1 - w y) / 2)
private theorem tm_eq (y : ℝ) : tm y = Real.sqrt ((1 - w y) / 2) := rfl
private noncomputable def tp (y : ℝ) : ℝ := Real.sqrt ((1 + w y) / 2)
private theorem tp_eq (y : ℝ) : tp y = Real.sqrt ((1 + w y) / 2) := rfl

private theorem exp_bounds {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    3 / 4 < Real.exp (-y) ∧ Real.exp (-y) < 1 := by
  constructor
  · have h := Real.exp_lt_exp.mpr (neg_lt_neg hy.2)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at h
    norm_num at h
    exact h
  · simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hy.1)

private theorem w_bounds {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    0 < w y ∧ w y < 1 ∧ w y ^ 2 = 4 * Real.exp (-y) - 3 := by
  have hb := exp_bounds hy
  have hw : 0 < 4 * Real.exp (-y) - 3 := by linarith
  rw [w_eq]
  refine ⟨Real.sqrt_pos.mpr hw, ?_, Real.sq_sqrt hw.le⟩
  have hs := Real.sq_sqrt hw.le
  have hn := Real.sqrt_nonneg (4 * Real.exp (-y) - 3)
  nlinarith

private theorem branch_data {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    0 < tm y ∧ 0 < tp y ∧ tm y ≤ 1 ∧ tp y ≤ 1 ∧
      tm y ^ 2 = (1 - w y) / 2 ∧ tp y ^ 2 = (1 + w y) / 2 := by
  have hw := w_bounds hy
  have hm : 0 < (1 - w y) / 2 := by linarith
  have hp : 0 < (1 + w y) / 2 := by linarith
  rw [tm_eq, tp_eq]
  have hms := Real.sq_sqrt hm.le
  have hps := Real.sq_sqrt hp.le
  refine ⟨Real.sqrt_pos.mpr hm, Real.sqrt_pos.mpr hp, ?_, ?_, hms, hps⟩
  · nlinarith [Real.sqrt_nonneg ((1 - w y) / 2)]
  · nlinarith [Real.sqrt_nonneg ((1 + w y) / 2)]

private theorem branch_q {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    q (tm y) = Real.exp (-y) ∧ q (tp y) = Real.exp (-y) := by
  have hw := (w_bounds hy).2.2
  have hb := branch_data hy
  have hm := hb.2.2.2.2.1
  have hp := hb.2.2.2.2.2
  simp only [q_eq, show ∀ t : ℝ, t ^ 4 = (t ^ 2) ^ 2 by intro t; ring]
  constructor
  · rw [hm]; nlinarith
  · rw [hp]; nlinarith

private theorem zC_eq (y : ℝ) : zC y = Real.sqrt (4 - 3 * Real.exp y) := rfl

private theorem nnDensity_eq (y : ℝ) : nnDensity y =
    if 0 < y ∧ y < Real.log (4 / 3) then
      3 * Real.exp (-y / 2) / (4 * zC y * Real.sqrt (2 * (Real.exp y - 1))) *
        ((Real.exp (y / 2) + zC y) * Real.sqrt (1 - Real.exp (-y / 2) * zC y) +
          (Real.exp (y / 2) - zC y) * Real.sqrt (1 + Real.exp (-y / 2) * zC y))
    else 0 := rfl

private theorem density_branch {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    nnDensity y = 3 * Real.exp (-y) * (tm y + tp y) / (2 * w y) := by
  have hw := w_bounds hy
  have hb := branch_data hy
  have hm := hb.2.2.2.2.1
  have hp := hb.2.2.2.2.2
  have he : 0 < Real.exp (y / 2) := Real.exp_pos _
  have he2 : Real.exp (y / 2) ^ 2 = Real.exp y := by
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  have heu : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hneg : Real.exp (-y / 2) = (Real.exp (y / 2))⁻¹ := by
    rw [show -y / 2 = -(y / 2) by ring, Real.exp_neg]
  have heyb : Real.exp y < 4 / 3 := by
    have h := Real.exp_lt_exp.mpr hy.2
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at h
  have hz : zC y = Real.exp (y / 2) * w y := by
    apply (sq_eq_sq₀ (by rw [zC_eq]; positivity) (mul_pos he hw.1).le).mp
    rw [zC_eq, Real.sq_sqrt (by linarith), mul_pow, hw.2.2, he2]
    nlinarith [heu]
  have hzw : Real.exp (-y / 2) * zC y = w y := by
    rw [hneg, hz, ← mul_assoc, inv_mul_cancel₀ he.ne', one_mul]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsm : Real.sqrt (1 - w y) = Real.sqrt 2 * tm y := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_pos hspos hb.1).le).mp
    rw [Real.sq_sqrt (by linarith [hw.2.1]), mul_pow, hs2, hm]
    ring
  have hsp : Real.sqrt (1 + w y) = Real.sqrt 2 * tp y := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_pos hspos hb.2.1).le).mp
    rw [Real.sq_sqrt (by linarith [hw.1]), mul_pow, hs2, hp]
    ring
  have hd : Real.sqrt (2 * (Real.exp y - 1)) =
      Real.sqrt 2 * Real.exp (y / 2) * tm y * tp y := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_pos (mul_pos (mul_pos hspos he) hb.1) hb.2.1).le).mp
    have hey1 : 1 < Real.exp y := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hy.1
    rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow, mul_pow, hs2, hm, hp, he2]
    nlinarith [congrArg (fun x : ℝ => Real.exp y * x) hw.2.2]
  have hbr :
      (Real.exp (y / 2) + Real.exp (y / 2) * w y) * (Real.sqrt 2 * tm y) +
        (Real.exp (y / 2) - Real.exp (y / 2) * w y) * (Real.sqrt 2 * tp y) =
      2 * Real.sqrt 2 * Real.exp (y / 2) * tm y * tp y * (tm y + tp y) := by
    have hm' : 1 - w y = 2 * tm y ^ 2 := by linarith
    have hp' : 1 + w y = 2 * tp y ^ 2 := by linarith
    calc
      _ = Real.exp (y / 2) * Real.sqrt 2 *
          ((1 + w y) * tm y + (1 - w y) * tp y) := by ring
      _ = _ := by rw [hm', hp']; ring
  rw [nnDensity_eq, if_pos ⟨hy.1, hy.2⟩, hzw, hsm, hsp, hd, hz, hneg, hbr]
  have hm0 := hb.1.ne'
  have hp0 := hb.2.1.ne'
  have hw0 := hw.1.ne'
  field_simp (disch := first | assumption | positivity)
  rw [he2]
  nlinarith [congrArg (fun x : ℝ => x * (tm y + tp y)) heu]

private theorem w_deriv {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    HasDerivAt w (-2 * Real.exp (-y) / w y) y := by
  have hb := exp_bounds hy
  have hr : 4 * Real.exp (-y) - 3 ≠ 0 := by linarith
  have h := ((((hasDerivAt_id y).neg.exp).const_mul 4).sub_const 3).sqrt hr
  simp only [Pi.neg_apply, id_eq] at h
  convert h using 1 <;> try rfl
  rw [w_eq]
  ring

private theorem branch_deriv {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    HasDerivAt tm (Real.exp (-y) / (2 * w y * tm y)) y ∧
      HasDerivAt tp (-Real.exp (-y) / (2 * w y * tp y)) y := by
  have hw := w_bounds hy
  have hb := branch_data hy
  have hm : (1 - w y) / 2 ≠ 0 := by linarith [hw.2.1]
  have hp : (1 + w y) / 2 ≠ 0 := by linarith [hw.1]
  constructor
  · have h := (((w_deriv hy).const_sub 1).div_const 2).sqrt hm
    convert h using 1 <;> try rfl
    rw [tm_eq]
    field_simp (disch := first
      | exact hw.1.ne'
      | exact hb.1.ne'
      | exact hb.2.1.ne'
      | positivity)
  · have h := (((w_deriv hy).const_add 1).div_const 2).sqrt hp
    convert h using 1 <;> try rfl
    rw [tp_eq]
    field_simp (disch := first
      | exact hw.1.ne'
      | exact hb.1.ne'
      | exact hb.2.1.ne'
      | positivity)

private noncomputable def G (y : ℝ) : ℝ := F (tm y) - F (tp y)
private theorem G_eq (y : ℝ) : G y = F (tm y) - F (tp y) := rfl

private theorem G_deriv {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    HasDerivAt G (y * nnDensity y) y := by
  have hb := branch_data hy
  have hd := branch_deriv hy
  have h := ((F_deriv (tm y)).comp y hd.1).sub ((F_deriv (tp y)).comp y hd.2)
  rw [(branch_q hy).1, (branch_q hy).2, Real.log_exp] at h
  convert h using 1 <;> try rfl
  rw [density_branch hy]
  have hw0 := (w_bounds hy).1.ne'
  field_simp (disch := first | exact hw0 | exact hb.1.ne' | exact hb.2.1.ne' | positivity)
  ring

private theorem w_continuous : Continuous w := by
  change Continuous (fun y : ℝ => Real.sqrt (4 * Real.exp (-y) - 3))
  exact ((Real.continuous_exp.comp continuous_neg).const_mul 4 |>.sub continuous_const).sqrt

private theorem branch_continuous : Continuous tm ∧ Continuous tp := by
  constructor
  · change Continuous (fun y : ℝ => Real.sqrt ((1 - w y) / 2))
    exact ((continuous_const.sub w_continuous).div_const 2).sqrt
  · change Continuous (fun y : ℝ => Real.sqrt ((1 + w y) / 2))
    exact ((continuous_const.add w_continuous).div_const 2).sqrt

private theorem G_continuous : Continuous G := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun t => (F_deriv t).continuousAt
  change Continuous (fun y : ℝ => F (tm y) - F (tp y))
  exact (hF.comp branch_continuous.1).sub (hF.comp branch_continuous.2)

private theorem G_endpoints :
    G 0 = -(10 / 3 - Real.pi) ∧ G (Real.log (4 / 3)) = 0 := by
  have hw0 : w 0 = 1 := by rw [w_eq]; norm_num
  have hwa : w (Real.log (4 / 3)) = 0 := by
    rw [w_eq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  constructor
  · rw [G_eq, tm_eq, tp_eq, hw0]
    norm_num only [sub_self, zero_div, Real.sqrt_zero, one_add_one_eq_two, div_self,
      Real.sqrt_one, F_zero, F_one, zero_sub]
  · rw [G_eq, tm_eq, tp_eq, hwa, sub_zero, add_zero, sub_self]

private theorem density_bound {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    0 ≤ nnDensity y ∧
      nnDensity y ≤ Real.sqrt 3 / Real.sqrt (Real.log (4 / 3) - y) := by
  have hw := w_bounds hy
  have hb := branch_data hy
  have he := exp_bounds hy
  have hmpos := hb.1
  have hppos := hb.2.1
  have hwpos := hw.1
  have hd : 0 < Real.log (4 / 3 : ℝ) - y := sub_pos.mpr hy.2
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrel : 4 * Real.exp (-y) = 3 * Real.exp (Real.log (4 / 3) - y) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3), Real.exp_neg]
    ring
  have hl : 3 * (Real.log (4 / 3 : ℝ) - y) ≤ w y ^ 2 := by
    nlinarith [Real.add_one_le_exp (Real.log (4 / 3) - y)]
  have hwl : Real.sqrt 3 * Real.sqrt (Real.log (4 / 3) - y) ≤ w y := by
    apply (sq_le_sq₀ (by positivity) hw.1.le).mp
    rw [mul_pow, hs3, Real.sq_sqrt hd.le]
    exact hl
  rw [density_branch hy]
  refine ⟨by positivity, ?_⟩
  have hnum : 3 * Real.exp (-y) * (tm y + tp y) ≤ 6 := by
    calc
      _ ≤ 3 * Real.exp (-y) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hb.2.2.1, hb.2.2.2.1]) (by positivity)
      _ ≤ 6 := by linarith [he.2]
  calc
    _ ≤ 6 / (2 * w y) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 3 / w y := by ring
    _ ≤ Real.sqrt 3 / Real.sqrt (Real.log (4 / 3) - y) := by
      apply (div_le_div_iff₀ hw.1 (Real.sqrt_pos.mpr hd)).mpr
      have h := mul_le_mul_of_nonneg_left hwl (Real.sqrt_nonneg 3)
      calc
        3 * Real.sqrt (Real.log (4 / 3) - y) =
            Real.sqrt 3 * (Real.sqrt 3 * Real.sqrt (Real.log (4 / 3) - y)) := by
          rw [← mul_assoc, ← pow_two, hs3]
        _ ≤ _ := h

private theorem integrand_bound {y : ℝ} (hy : y ∈ Ioo 0 (Real.log (4 / 3))) :
    0 ≤ y * nnDensity y ∧ y * nnDensity y ≤
      Real.log (4 / 3) * Real.sqrt 3 / Real.sqrt (Real.log (4 / 3) - y) := by
  have hb := density_bound hy
  refine ⟨mul_nonneg hy.1.le hb.1, ?_⟩
  calc
    _ ≤ y * (Real.sqrt 3 / Real.sqrt (Real.log (4 / 3) - y)) :=
      mul_le_mul_of_nonneg_left hb.2 hy.1.le
    _ ≤ Real.log (4 / 3) * (Real.sqrt 3 / Real.sqrt (Real.log (4 / 3) - y)) :=
      mul_le_mul_of_nonneg_right hy.2.le (by positivity)
    _ = _ := by ring

private theorem integrand_continuousOn :
    ContinuousOn (fun y : ℝ => y * nnDensity y) (Ioo 0 (Real.log (4 / 3))) := by
  have hc : ContinuousOn (fun y : ℝ => y *
      (3 * Real.exp (-y) * (tm y + tp y) / (2 * w y))) (Ioo 0 (Real.log (4 / 3))) := by
    apply continuous_id.continuousOn.mul
    apply ((((Real.continuous_exp.comp continuous_neg).const_mul 3).mul
      (branch_continuous.1.add branch_continuous.2)).continuousOn).div
      ((w_continuous.const_mul 2).continuousOn)
    intro y hy
    exact mul_ne_zero (by norm_num) (w_bounds hy).1.ne'
  apply hc.congr
  intro y hy
  change y * nnDensity y = _
  rw [density_branch hy]

private theorem integrand_integrableOn :
    IntegrableOn (fun y : ℝ => y * nnDensity y) (Ioo 0 (Real.log (4 / 3))) := by
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume
      0 (Real.log (4 / 3)) := intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have href : IntervalIntegrable
      (fun y : ℝ => (Real.log (4 / 3) - y) ^ (-(1 / 2 : ℝ))) volume 0
      (Real.log (4 / 3)) := by
    simpa only [sub_self, sub_zero] using (hr.comp_sub_left (Real.log (4 / 3))).symm
  have hmaj := href.const_mul (Real.log (4 / 3) * Real.sqrt 3)
  have hmajOn := (intervalIntegrable_iff_integrableOn_Ioo_of_le a_pos.le).mp hmaj
  apply hmajOn.mono' (integrand_continuousOn.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hb := integrand_bound hy
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  rw [Real.rpow_neg (sub_pos.mpr hy.2).le, ← Real.sqrt_eq_rpow]
  simpa only [div_eq_mul_inv] using hb.2

private theorem integrand_zero (y : ℝ) (hy : y ∉ Ioo 0 (Real.log (4 / 3))) :
    y * nnDensity y = 0 := by
  have h : ¬ (0 < y ∧ y < Real.log (4 / 3)) := hy
  rw [nnDensity_eq, if_neg h, mul_zero]

private theorem G_limits :
    Tendsto G (𝓝[>] 0) (𝓝 (-(10 / 3 - Real.pi))) ∧
      Tendsto G (𝓝[<] (Real.log (4 / 3))) (𝓝 0) := by
  constructor
  · rw [← G_endpoints.1]
    exact tendsto_nhdsWithin_of_tendsto_nhds G_continuous.continuousAt.tendsto
  · rw [← G_endpoints.2]
    exact tendsto_nhdsWithin_of_tendsto_nhds G_continuous.continuousAt.tendsto

private theorem interval_mean :
    ∫ y in (0 : ℝ)..Real.log (4 / 3), y * nnDensity y = 10 / 3 - Real.pi := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le a_pos.le).mpr
    integrand_integrableOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto a_pos
    (fun y hy => G_deriv hy) hi G_limits.1 G_limits.2]
  ring

/-- The literal Appendix C density has integrable first moment 10/3 − π. -/
theorem result : claim := by
  change Integrable (fun y : ℝ => y * nnDensity y) ∧
    ∫ y : ℝ, y * nnDensity y = 10 / 3 - Real.pi
  refine ⟨integrand_integrableOn.integrable_of_forall_notMem_eq_zero integrand_zero, ?_⟩
  have h := interval_mean
  rw [intervalIntegral.integral_of_le a_pos.le, integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_integral_of_forall_compl_eq_zero integrand_zero] at h
  exact h

end D5.S3.Quantum.Magic.NonlocalNonstabilizernessHaarMean
