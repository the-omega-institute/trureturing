/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterRightLimit
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Leading terms of the BMV divided differences as the last root grows. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenter
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

/-! # Asymptotics of the divided differences in the BMV right boundary -/

open Filter
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

open DividedDifference (homogeneousThree clear_distinct clear_repeat_first clear_repeat_last)

/-- The contribution of the largest node to the second divided difference. -/
private def leading (p : ℕ) (a b y : ℝ) : ℝ :=
  y ^ (p + 2) / ((y - a) * (y - b))

private theorem inverse_gap_tendsto_zero (a : ℝ) :
    Tendsto (fun y : ℝ ↦ (y - a)⁻¹) atTop (𝓝 0) := by
  have hg : Tendsto (fun y : ℝ ↦ y - a) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-a) tendsto_id
  exact tendsto_inv_atTop_zero.comp hg

/-- All contributions other than the largest node tend to zero,
also when the other two nodes coincide. -/
theorem homogeneousThree_sub_leading_tendsto_zero (p : ℕ) (a b : ℝ) :
    Tendsto (fun y ↦ homogeneousThree p a b y - leading p a b y) atTop (𝓝 0) := by
  by_cases hab : a = b
  · subst b
    have hi := inverse_gap_tendsto_zero a
    have hlim : Tendsto (fun y : ℝ ↦
        (y - a)⁻¹ * (-((p : ℝ) + 2) * a ^ (p + 1)) -
          ((y - a)⁻¹) ^ 2 * a ^ (p + 2)) atTop (𝓝 0) := by
      simpa only [zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
        (hi.mul_const _).sub ((hi.pow 2).mul_const _)
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop a] with y hy
    have hgap : y - a ≠ 0 := sub_ne_zero.mpr hy.ne'
    have hp := clear_repeat_first p a y
    unfold leading
    field_simp [hgap]
    linear_combination -hp
  · have ha := inverse_gap_tendsto_zero a
    have hb := inverse_gap_tendsto_zero b
    have hlim : Tendsto (fun y : ℝ ↦
        (y - a)⁻¹ * (a ^ (p + 2) / (b - a)) -
          (y - b)⁻¹ * (b ^ (p + 2) / (b - a))) atTop (𝓝 0) := by
      simpa only [zero_mul, sub_zero] using
        (ha.mul_const _).sub (hb.mul_const _)
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (max a b)] with y hy
    have hay : a < y := (le_max_left a b).trans_lt hy
    have hby : b < y := (le_max_right a b).trans_lt hy
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hya : y - a ≠ 0 := sub_ne_zero.mpr hay.ne'
    have hyb : y - b ≠ 0 := sub_ne_zero.mpr hby.ne'
    have hp := clear_distinct p a b y
    unfold leading
    field_simp [hba, hya, hyb]
    linear_combination -hp

/-- The coefficient of the highest power when the last two nodes coincide. -/
theorem homogeneousThree_repeat_last_tendsto (p : ℕ) (a : ℝ) :
    Tendsto (fun y ↦ homogeneousThree p a y y / y ^ p) atTop
      (𝓝 ((p : ℝ) + 1)) := by
  have hi : Tendsto (fun y : ℝ ↦ a / y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := a)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ ↦ y⁻¹) atTop (𝓝 0))
  have hden : Tendsto (fun y : ℝ ↦ (1 - a / y) ^ 2) atTop (𝓝 1) := by
    simpa only [sub_zero, one_pow] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hi).pow 2
  have hnum : Tendsto (fun y : ℝ ↦
      (a / y) ^ (p + 2) - ((p : ℝ) + 2) * (a / y) + ((p : ℝ) + 1))
      atTop (𝓝 ((p : ℝ) + 1)) := by
    have hp : p + 2 ≠ 0 := by omega
    simpa only [zero_pow hp, mul_zero, sub_zero, zero_add] using
      ((hi.pow (p + 2)).sub ((tendsto_const_nhds (x := (p : ℝ) + 2)).mul hi)).add
        (tendsto_const_nhds (x := (p : ℝ) + 1))
  have hlim := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (max a 0)] with y hy
  have hay : a < y := (le_max_left a 0).trans_lt hy
  have hy0 : y ≠ 0 := ((le_max_right a 0).trans_lt hy).ne'
  have hgap : y - a ≠ 0 := sub_ne_zero.mpr hay.ne'
  change ((a / y) ^ (p + 2) - ((p : ℝ) + 2) * (a / y) + ((p : ℝ) + 1)) /
    (1 - a / y) ^ 2 = homogeneousThree p a y y / y ^ p
  rw [show 1 - a / y = (y - a) / y by field_simp [hy0]]
  have hp := clear_repeat_last p a y
  rw [div_pow, div_pow, pow_add y p 2]
  field_simp [hy0, hgap]
  linear_combination -hp

private theorem const_div_tendsto_zero (a : ℝ) :
    Tendsto (fun y : ℝ ↦ a / y) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds (x := a)).mul
      (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ ↦ y⁻¹) atTop (𝓝 0))

/-- The largest-node contribution has leading coefficient one. -/
theorem leading_div_pow_tendsto_one (p : ℕ) (a b : ℝ) :
    Tendsto (fun y ↦ leading p a b y / y ^ p) atTop (𝓝 1) := by
  have ha : Tendsto (fun y : ℝ ↦ 1 - a / y) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (const_div_tendsto_zero a)
  have hb : Tendsto (fun y : ℝ ↦ 1 - b / y) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (const_div_tendsto_zero b)
  have h : Tendsto (fun y : ℝ ↦ ((1 - a / y) * (1 - b / y))⁻¹) atTop (𝓝 1) := by
    simpa only [one_mul, inv_one] using
      (ha.mul hb).inv₀ (by simp : 1 * (1 : ℝ) ≠ 0)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (max a b))] with y hy
  have hy₀ : y ≠ 0 := ((le_max_left 0 (max a b)).trans_lt hy).ne'
  have hy₁ : y - a ≠ 0 := sub_ne_zero.mpr
    (((le_max_left a b).trans (le_max_right 0 (max a b))).trans_lt hy).ne'
  have hy₂ : y - b ≠ 0 := sub_ne_zero.mpr
    (((le_max_right a b).trans (le_max_right 0 (max a b))).trans_lt hy).ne'
  rw [show 1 - a / y = (y - a) / y by field_simp [hy₀],
    show 1 - b / y = (y - b) / y by field_simp [hy₀]]
  unfold leading
  rw [pow_add y p 2]
  field_simp [hy₀, hy₁, hy₂]

open DimThree (defect)

private theorem cube_tendsto_atTop :
    Tendsto (fun y : ℝ ↦ y ^ (3 : ℕ)) atTop atTop :=
  tendsto_pow_atTop (by decide)

/-- After removing the largest-node contribution, the comparison term
is the only term of order equal to the p-th power of the last root. -/
theorem defect_sub_leading_div_pow_tendsto {p : ℕ} (hp : 0 < p) (a x : ℝ) :
    Tendsto (fun y ↦ (defect p a x y - leading p (a ^ 3) (x ^ 3) (y ^ 3)) / y ^ p)
      atTop (𝓝 (-((p + 2).choose 2 : ℝ) * (a * x) ^ p)) := by
  have h₁ := (homogeneousThree_sub_leading_tendsto_zero p (a ^ 3) (x ^ 3)).comp
    cube_tendsto_atTop
  have h₂ : Tendsto (fun y : ℝ ↦ (y ^ p)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hp.ne')
  have h := (h₁.mul h₂).sub
    (tendsto_const_nhds (x := ((p + 2).choose 2 : ℝ) * (a * x) ^ p))
  simp only [zero_mul, zero_sub, Function.comp_def] at h
  rw [neg_mul]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [DividedDifference.defect_eq_homogeneous, mul_pow]
  field_simp [hy.ne']
  ring

/-- The repeated-last defect retains its highest-order coefficient because
the subtracted comparison term contains only two powers of the last root. -/
theorem defect_repeat_last_div_cube_pow_tendsto {p : ℕ} (hp : 0 < p) (a : ℝ) :
    Tendsto (fun y ↦ defect p a y y / (y ^ 3) ^ p) atTop (𝓝 ((p : ℝ) + 1)) := by
  have hH := (homogeneousThree_repeat_last_tendsto p (a ^ 3)).comp cube_tendsto_atTop
  have hi : Tendsto (fun y : ℝ ↦ (y ^ p)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hp.ne')
  have ht := hH.sub (hi.mul_const (((p + 2).choose 2 : ℝ) * a ^ p))
  simp only [zero_mul, sub_zero, Function.comp_def] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [DividedDifference.defect_eq_homogeneous, mul_pow, mul_pow, ← pow_mul]
  rw [show 3 * p = p + p + p by omega, pow_add y (p + p) p, pow_add y p p]
  field_simp [hy.ne'] <;> ring

private theorem cube_pow (p : ℕ) (y : ℝ) : (y ^ 3) ^ p = (y ^ p) ^ 3 := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 p]

private theorem defect_div_pow3_tendsto_one {p : ℕ} (hp : 0 < p) (a x : ℝ) :
    Tendsto (fun y ↦ defect p a x y / (y ^ p) ^ 3) atTop (𝓝 1) := by
  have h := (leading_div_pow_tendsto_one p (a ^ 3) (x ^ 3)).comp cube_tendsto_atTop
  simp only [Function.comp_def, cube_pow p] at h
  have hi : Tendsto (fun y : ℝ ↦ (y ^ p)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hp.ne')
  have hlim := ((defect_sub_leading_div_pow_tendsto hp a x).mul (hi.pow 2)).add h
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp [hy.ne']
  ring

private theorem sqrt_normalized_product (P Q s : ℝ) (hs : 0 < s) :
    Real.sqrt ((P / s) * (Q / s)) = Real.sqrt (P * Q) / s := by
  rw [show (P / s) * (Q / s) = (P * Q) / s ^ 2 by field_simp [hs.ne'],
    Real.sqrt_div' _ (sq_nonneg s), Real.sqrt_sq hs.le]

private theorem normalized_rationalized_sub {P Q R S T s : ℝ}
    (hPQ : 0 ≤ P * Q) (hT : 0 < T) (hrs : R * S = T ^ 2) (hs : 0 < s) :
    (Real.sqrt (P * Q) - T) / s =
      (((P - R) / s) * (Q / s ^ 3) + (R / s ^ 3) * ((Q - S) / s)) /
        (Real.sqrt ((P / s ^ 3) * (Q / s ^ 3)) + T / s ^ 3) := by
  rw [sqrt_normalized_product P Q (s ^ 3) (pow_pos hs 3)]
  have hden : 0 < Real.sqrt (P * Q) + T :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hT
  have he : Real.sqrt (P * Q) / s ^ 3 + T / s ^ 3 ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero hden.ne' (pow_pos hs 3).ne'
  have hsq := Real.sq_sqrt hPQ
  field_simp [hs.ne', hden.ne', he]
  nlinarith only [hsq, hrs]

/-- The normalized kernel tends to zero at an unbounded upper root. -/
theorem kernel_tendsto_right {p : ℕ} (hp : 0 < p) {a x : ℝ}
    (ha : 0 < a) (hax : a < x) :
    Tendsto (fun y ↦ Extreme.normalized (fun t ↦ defect p a t t) (fun t ↦ defect p a t t)
      (defect p a) (fun t y ↦ defect p a a y * defect p t t y) x y) atTop (𝓝 0) := by
  let s (y : ℝ) := y ^ p
  let P (y : ℝ) := defect p a a y
  let Q (y : ℝ) := defect p x x y
  let T (y : ℝ) := leading p (a ^ 3) (x ^ 3) (y ^ 3)
  let R (y : ℝ) := leading p (a ^ 3) (a ^ 3) (y ^ 3)
  let S (y : ℝ) := leading p (x ^ 3) (x ^ 3) (y ^ 3)
  let N : ℝ := (p + 2).choose 2
  have hx : 0 < x := ha.trans hax
  have hpTop : Tendsto s atTop atTop := tendsto_pow_atTop hp.ne'
  have hP : Tendsto (fun y ↦ P y / (s y) ^ 3) atTop (𝓝 1) :=
    defect_div_pow3_tendsto_one hp a a
  have hQ : Tendsto (fun y ↦ Q y / (s y) ^ 3) atTop (𝓝 1) :=
    defect_div_pow3_tendsto_one hp x x
  have hT : Tendsto (fun y ↦ T y / (s y) ^ 3) atTop (𝓝 1) := by
    simpa only [T, s, Function.comp_def, cube_pow p] using
      (leading_div_pow_tendsto_one p (a ^ 3) (x ^ 3)).comp cube_tendsto_atTop
  have hR : Tendsto (fun y ↦ R y / (s y) ^ 3) atTop (𝓝 1) := by
    simpa only [R, s, Function.comp_def, cube_pow p] using
      (leading_div_pow_tendsto_one p (a ^ 3) (a ^ 3)).comp cube_tendsto_atTop
  have hPR : Tendsto (fun y ↦ (P y - R y) / s y) atTop (𝓝 (-N * (a * a) ^ p)) :=
    defect_sub_leading_div_pow_tendsto hp a a
  have hQS : Tendsto (fun y ↦ (Q y - S y) / s y) atTop (𝓝 (-N * (x * x) ^ p)) :=
    defect_sub_leading_div_pow_tendsto hp x x
  have hz : Tendsto (fun y ↦ Real.sqrt ((P y / (s y) ^ 3) * (Q y / (s y) ^ 3)) +
                      T y / (s y) ^ 3) atTop (𝓝 2) := by
    simpa only [one_mul, Real.sqrt_one, show (1 : ℝ) + 1 = 2 by norm_num] using
      (hP.mul hQ).sqrt.add hT
  have hr := ((hPR.mul hQ).add (hR.mul hQS)).div hz (by norm_num : (2 : ℝ) ≠ 0)
  have hrad : Tendsto (fun y ↦ (Real.sqrt (P y * Q y) - T y) / s y) atTop
      (𝓝 (((-N * (a * a) ^ p) * 1 + 1 * (-N * (x * x) ^ p)) / 2)) := by
    refine hr.congr' ?_
    filter_upwards [eventually_gt_atTop x] with y hy
    have hy₀ : 0 < y := hx.trans hy
    have hsa : a ^ 3 < y ^ 3 := by gcongr <;> linarith
    have hsx : x ^ 3 < y ^ 3 := by gcongr
    have hpos : 0 < T y := by
      exact div_pos (pow_pos (pow_pos hy₀ 3) _) (mul_pos (sub_pos.mpr hsa) (sub_pos.mpr hsx))
    have hsq : R y * S y = (T y) ^ 2 := by
      dsimp [R, S, T, leading]
      field_simp [(sub_pos.mpr hsa).ne', (sub_pos.mpr hsx).ne']
      <;> ring
    have hnonneg : 0 ≤ P y * Q y := mul_nonneg
      (UniformThreeSpectrum.defect_nonneg_all p _ _ _ ha.le ha.le hy₀.le)
      (UniformThreeSpectrum.defect_nonneg_all p _ _ _ hx.le hx.le hy₀.le)
    exact (normalized_rationalized_sub hnonneg hpos hsq (pow_pos hy₀ _)).symm
  have hD := defect_sub_leading_div_pow_tendsto hp a x
  have hdiff := hD.sub hrad
  have hnormalized :
      (fun y ↦ (defect p a x y - T y) / s y - (Real.sqrt (P y * Q y) - T y) / s y) =
      (fun y ↦ (defect p a x y - Real.sqrt (P y * Q y)) / s y) := by
    funext y
    ring
  change Tendsto _ atTop _ at hdiff
  rw [hnormalized] at hdiff
  have hrepeat : Tendsto (fun y ↦ defect p a y y / (s y) ^ 3) atTop (𝓝 ((p : ℝ) + 1)) := by
    simpa only [s, cube_pow p] using defect_repeat_last_div_cube_pow_tendsto hp a
  have hz₁ : 0 < Real.sqrt (defect p a x x) := Real.sqrt_pos.mpr (weight_pos hp ha.le hax)
  have hz₂ : 0 < Real.sqrt ((p : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hden := (tendsto_const_nhds (x := Real.sqrt (defect p a x x))).mul hrepeat.sqrt
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hpTop)
  have ht := (hdiff.div hden (mul_pos hz₁ hz₂).ne').mul hi
  simp only [mul_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop x] with y hy
  have hsy : 0 < s y := pow_pos (hx.trans hy) p
  have hW := weight_pos hp ha.le (hax.trans hy)
  have hs₁ : Real.sqrt (s y) ≠ 0 := (Real.sqrt_pos.mpr hsy).ne'
  have hs₃ : Real.sqrt ((s y) ^ 3) = s y * Real.sqrt (s y) := by
    rw [show (s y) ^ 3 = (s y) ^ 2 * s y by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hsy.le]
  change
    ((defect p a x y - Real.sqrt (P y * Q y)) / s y) /
        (Real.sqrt (defect p a x x) * Real.sqrt (defect p a y y / (s y) ^ 3)) *
      (Real.sqrt (s y))⁻¹ =
    Extreme.normalized (fun t ↦ defect p a t t) (fun t ↦ defect p a t t)
      (defect p a) (fun t y ↦ defect p a a y * defect p t t y) x y
  simp only [Extreme.normalized, P, Q, Real.sqrt_div hW.le, hs₃]
  field_simp [hsy.ne', hs₁, hz₁.ne', (Real.sqrt_pos.mpr hW).ne']
  <;> ring

#print axioms kernel_tendsto_right

end RefinedBMV.PositiveCenter
