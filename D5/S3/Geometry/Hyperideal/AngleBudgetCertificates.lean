/- GID: D5/S3/Geometry/Hyperideal/AngleBudgetCertificates
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/AngleBudgetCertificates
   mirror-E: none(waiver:cfmp-angle-budget-certificates)
   anchors: []
   utility: none
   digest: Exact strict angle budgets for the five CFMP Section 25.3 certificates. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.AngleBudgetCertificates

def betaTwo : ℝ := Real.arccos (70 / 99)

def betaThree : ℝ := Real.arccos (49 * Real.sqrt 6 / 198)

def thetaZero : ℝ := Real.arccos (31 / 33)

def thetaOne : ℝ := Real.arccos (25 / Real.sqrt 726)

def thetaTwo : ℝ := Real.arccos (81 / 88)

private lemma cos_gt_of_quarter_sin_bound (r q : ℝ)
    (hr : 0 ≤ r / 4) (hrpi : r / 4 ≤ Real.pi)
    (hrhalfpi : r / 2 ≤ Real.pi / 2)
    (hrsmall : |r / 4| ≤ 1)
    (hcosHalfNonneg : 0 ≤
      1 - 2 * ((r / 4) - (r / 4)^3 / 6 + |r / 4|^5 / 100)^2)
    (hq : q < 2 * (1 - 2 * ((r / 4) - (r / 4)^3 / 6 +
      |r / 4|^5 / 100)^2)^2 - 1) :
    q < Real.cos r := by
  have hsin := Real.sin_bound hrsmall
  have hsinUpper : Real.sin (r / 4) ≤
      r / 4 - (r / 4)^3 / 6 + |r / 4|^5 / 100 := by
    have hh := (abs_sub_le_iff.mp hsin).1
    linarith
  have hsinNonneg : 0 ≤ Real.sin (r / 4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr hrpi
  have hnumeric : 0 ≤ r / 4 - (r / 4)^3 / 6 + |r / 4|^5 / 100 := by
    rw [abs_of_nonneg hr]
    have hy : r / 4 ≤ 1 := le_trans (le_abs_self _) hrsmall
    have hy2 : (r / 4)^2 ≤ 1 := by nlinarith [sq_nonneg (r / 4)]
    have hfactor : 0 ≤ 1 - (r / 4)^2 / 6 + (r / 4)^4 / 100 := by
      nlinarith [sq_nonneg ((r / 4)^2)]
    convert mul_nonneg hr hfactor using 1 <;> ring
  have hsq : Real.sin (r / 4)^2 ≤
      (r / 4 - (r / 4)^3 / 6 + |r / 4|^5 / 100)^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hsinUpper)
      (add_nonneg hnumeric hsinNonneg)
    nlinarith
  have hhalfLower : 1 - 2 *
      (r / 4 - (r / 4)^3 / 6 + |r / 4|^5 / 100)^2 ≤
      Real.cos (r / 2) := by
    calc
      1 - 2 * (r / 4 - (r / 4)^3 / 6 + |r / 4|^5 / 100)^2 ≤
          1 - 2 * Real.sin (r / 4)^2 := by nlinarith
      _ = Real.cos (r / 2) := by
        calc
          1 - 2 * Real.sin (r / 4)^2 = Real.cos (2 * (r / 4)) := by
            rw [Real.cos_two_mul_eq_one_sub]
          _ = Real.cos (r / 2) := by congr 1 <;> ring
  have hhalfNonneg : 0 ≤ Real.cos (r / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hcosEq : Real.cos r = 2 * Real.cos (r / 2)^2 - 1 := by
    calc
      Real.cos r = Real.cos (2 * (r / 2)) := by congr 1 <;> ring
      _ = 2 * Real.cos (r / 2)^2 - 1 := by
        rw [Real.cos_two_mul]
  rw [hcosEq]
  have hprod := mul_nonneg (sub_nonneg.mpr hhalfLower)
    (add_nonneg hhalfNonneg hcosHalfNonneg)
  nlinarith

private lemma arccos_gt_of_cos_gt {r q : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hq0 : (-1 : ℝ) ≤ q)
    (hcos : q < Real.cos r) :
    r < Real.arccos q := by
  have h := Real.arccos_lt_arccos hq0 hcos (Real.cos_le_one r)
  rw [Real.arccos_cos hr0 hrpi] at h
  exact h

private lemma betaTwo_lower : (7854 / 10000 : ℝ) < betaTwo := by
  unfold betaTwo
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by norm_num)
  have hhalf : 0 ≤ 1 - 2 * ((7854 / 10000 : ℝ) / 4 -
      ((7854 / 10000 : ℝ) / 4)^3 / 6 +
      |(7854 / 10000 : ℝ) / 4|^5 / 100)^2 := by
    norm_num [abs_of_nonneg]
  apply cos_gt_of_quarter_sin_bound
  · norm_num [abs_of_nonneg]
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]
  · norm_num
  · exact hhalf
  · norm_num [abs_of_nonneg]

private lemma betaThree_lower : (9195 / 10000 : ℝ) < betaThree := by
  unfold betaThree
  have hsqrtPos : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtUpper : Real.sqrt (6 : ℝ) < (24496 / 10000 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
    nlinarith [Real.sqrt_nonneg (6 : ℝ)]
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by nlinarith [Real.sqrt_nonneg (6 : ℝ)])
  have hhalf : 0 ≤ 1 - 2 * ((9195 / 10000 : ℝ) / 4 -
      ((9195 / 10000 : ℝ) / 4)^3 / 6 +
      |(9195 / 10000 : ℝ) / 4|^5 / 100)^2 := by
    norm_num [abs_of_nonneg]
  apply cos_gt_of_quarter_sin_bound
  · norm_num
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]
  · norm_num
  · exact hhalf
  · apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 198)).2
    have hs : 49 * Real.sqrt 6 < (1200304 / 10000 : ℝ) := by
      nlinarith [hsqrtUpper]
    calc
      49 * Real.sqrt 6 < (1200304 / 10000 : ℝ) := hs
      _ < (2 * (1 - 2 * ((9195 / 10000 : ℝ) / 4 -
        ((9195 / 10000 : ℝ) / 4)^3 / 6 +
        |(9195 / 10000 : ℝ) / 4|^5 / 100)^2)^2 - 1) * 198 := by
          norm_num [abs_of_nonneg]

private lemma thetaZero_lower : (3499 / 10000 : ℝ) < thetaZero := by
  unfold thetaZero
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by norm_num)
  have hhalf : 0 ≤ 1 - 2 * ((3499 / 10000 : ℝ) / 4 -
      ((3499 / 10000 : ℝ) / 4)^3 / 6 +
      |(3499 / 10000 : ℝ) / 4|^5 / 100)^2 := by
    norm_num [abs_of_nonneg]
  apply cos_gt_of_quarter_sin_bound
  · norm_num
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]
  · norm_num
  · exact hhalf
  · norm_num [abs_of_nonneg]

private lemma thetaOne_lower : (3822 / 10000 : ℝ) < thetaOne := by
  unfold thetaOne
  have hsqrtPos : 0 < Real.sqrt (726 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLower : (673609 / 25000 : ℝ) < Real.sqrt (726 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 726)
    nlinarith [Real.sqrt_nonneg (726 : ℝ)]
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by
      have hq : 0 < 25 / Real.sqrt (726 : ℝ) :=
        div_pos (by norm_num) hsqrtPos
      linarith)
  have hhalf : 0 ≤ 1 - 2 * ((3822 / 10000 : ℝ) / 4 -
      ((3822 / 10000 : ℝ) / 4)^3 / 6 +
      |(3822 / 10000 : ℝ) / 4|^5 / 100)^2 := by
    norm_num [abs_of_nonneg]
  apply cos_gt_of_quarter_sin_bound
  · norm_num
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]
  · norm_num
  · exact hhalf
  · apply (div_lt_iff₀ hsqrtPos).2
    calc
      25 < (2 * (1 - 2 * ((3822 / 10000 : ℝ) / 4 -
        ((3822 / 10000 : ℝ) / 4)^3 / 6 +
        |(3822 / 10000 : ℝ) / 4|^5 / 100)^2)^2 - 1) *
          (673609 / 25000 : ℝ) := by norm_num [abs_of_nonneg]
      _ < (2 * (1 - 2 * ((3822 / 10000 : ℝ) / 4 -
        ((3822 / 10000 : ℝ) / 4)^3 / 6 +
        |(3822 / 10000 : ℝ) / 4|^5 / 100)^2)^2 - 1) * Real.sqrt 726 := by
        apply mul_lt_mul_of_pos_left hsqrtLower
        norm_num [abs_of_nonneg]

private lemma thetaTwo_lower : (4015 / 10000 : ℝ) < thetaTwo := by
  unfold thetaTwo
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by norm_num)
  have hhalf : 0 ≤ 1 - 2 * ((4015 / 10000 : ℝ) / 4 -
      ((4015 / 10000 : ℝ) / 4)^3 / 6 +
      |(4015 / 10000 : ℝ) / 4|^5 / 100)^2 := by
    norm_num [abs_of_nonneg]
  apply cos_gt_of_quarter_sin_bound
  · norm_num
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]
  · norm_num
  · exact hhalf
  · norm_num [abs_of_nonneg]

/-- The five strict angle budgets from the CFMP Section 25.3 certificate. -/
theorem exact_angle_budget_certificates :
    8 * betaTwo > 2 * Real.pi ∧
    6 * betaThree + betaTwo > 2 * Real.pi ∧
    18 * thetaZero > 2 * Real.pi ∧
    11 * thetaOne + 6 * thetaZero > 2 * Real.pi ∧
    9 * thetaTwo + 7 * thetaOne > 2 * Real.pi := by
  have hpi : Real.pi < (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    linarith
  have h1 : 8 * betaTwo > 2 * Real.pi := by
    nlinarith [betaTwo_lower]
  have h2 : 6 * betaThree + betaTwo > 2 * Real.pi := by
    nlinarith [betaThree_lower, betaTwo_lower]
  have h3 : 18 * thetaZero > 2 * Real.pi := by
    nlinarith [thetaZero_lower]
  have h4 : 11 * thetaOne + 6 * thetaZero > 2 * Real.pi := by
    nlinarith [thetaOne_lower, thetaZero_lower]
  have h5 : 9 * thetaTwo + 7 * thetaOne > 2 * Real.pi := by
    nlinarith [thetaTwo_lower, thetaOne_lower]
  exact ⟨h1, h2, h3, h4, h5⟩

#print axioms exact_angle_budget_certificates

end D5.S3.Geometry.Hyperideal.AngleBudgetCertificates
