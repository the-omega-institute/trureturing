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

private lemma cos_gt_of_sin_bound (r q : ℝ)
    (hr : 0 ≤ r / 2) (hrpi : r / 2 ≤ Real.pi)
    (hrsmall : |r / 2| ≤ 1)
    (hq : q < 1 - 2 * ((r / 2) - (r / 2)^3 / 6 + |r / 2|^5 / 100)^2) :
    q < Real.cos r := by
  have hsin := Real.sin_bound hrsmall
  have hsinUpper : Real.sin (r / 2) ≤
      r / 2 - (r / 2)^3 / 6 + |r / 2|^5 / 100 := by
    have hh := (abs_sub_le_iff.mp hsin).1
    linarith
  have hsinNonneg : 0 ≤ Real.sin (r / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr hrpi
  have hnumeric : 0 ≤ r / 2 - (r / 2)^3 / 6 + |r / 2|^5 / 100 := by
    have hrnonneg : 0 ≤ r := by linarith
    rw [abs_of_nonneg hr]
    nlinarith [sq_nonneg r, sq_nonneg (r - 1), sq_nonneg (r - 2)]
  have hsq : Real.sin (r / 2)^2 ≤
      (r / 2 - (r / 2)^3 / 6 + |r / 2|^5 / 100)^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hsinUpper)
      (add_nonneg hnumeric hsinNonneg)
    nlinarith
  have hcosEq : Real.cos r = 1 - 2 * Real.sin (r / 2)^2 := by
    have hr' : 2 * (r / 2) = r := by ring
    rw [← hr', Real.cos_two_mul_eq_one_sub]
  rw [hcosEq]
  nlinarith

private lemma arccos_gt_of_cos_gt {r q : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hq0 : (-1 : ℝ) ≤ q) (hq1 : q ≤ 1)
    (hcos : q < Real.cos r) :
    r < Real.arccos q := by
  have h := Real.arccos_lt_arccos hq0 hcos (Real.cos_le_one r)
  rw [Real.arccos_cos hr0 hrpi] at h
  exact h

private lemma betaTwo_lower : (7854 / 10000 : ℝ) < betaTwo := by
  unfold betaTwo
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by norm_num) (by norm_num)
  apply cos_gt_of_sin_bound (by norm_num) (by nlinarith [Real.pi_gt_three])
    (by norm_num)
  norm_num

private lemma betaThree_lower : (9195 / 10000 : ℝ) < betaThree := by
  unfold betaThree
  have hsqrtPos : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtUpper : Real.sqrt (6 : ℝ) < (49 / 20 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
    nlinarith [Real.sqrt_nonneg (6 : ℝ)]
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by positivity) (by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 198)).2
      nlinarith [hsqrtUpper])
  apply cos_gt_of_sin_bound (by norm_num) (by nlinarith [Real.pi_gt_three])
    (by norm_num)
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 198)).2
  nlinarith [hsqrtUpper]

private lemma thetaZero_lower : (3499 / 10000 : ℝ) < thetaZero := by
  unfold thetaZero
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by norm_num) (by norm_num)
  apply cos_gt_of_sin_bound (by norm_num) (by nlinarith [Real.pi_gt_three])
    (by norm_num)
  norm_num

private lemma thetaOne_lower : (3822 / 10000 : ℝ) < thetaOne := by
  unfold thetaOne
  have hsqrtPos : 0 < Real.sqrt (726 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtLower : (2694 / 100 : ℝ) < Real.sqrt (726 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 726)
    nlinarith [Real.sqrt_nonneg (726 : ℝ)]
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by positivity) (by
      apply (div_le_iff₀ hsqrtPos).2
      nlinarith [hsqrtLower])
  apply cos_gt_of_sin_bound (by norm_num) (by nlinarith [Real.pi_gt_three])
    (by norm_num)
  apply (div_lt_iff₀ hsqrtPos).2
  nlinarith [hsqrtLower]

private lemma thetaTwo_lower : (4015 / 10000 : ℝ) < thetaTwo := by
  unfold thetaTwo
  apply arccos_gt_of_cos_gt (by norm_num) (by norm_num; nlinarith [Real.pi_gt_three])
    (by norm_num) (by norm_num)
  apply cos_gt_of_sin_bound (by norm_num) (by nlinarith [Real.pi_gt_three])
    (by norm_num)
  norm_num

/-- The five strict angle budgets from the CFMP Section 25.3 certificate. -/
theorem exact_angle_budget_certificates :
    8 * betaTwo > 2 * Real.pi ∧
    6 * betaThree + betaTwo > 2 * Real.pi ∧
    18 * thetaZero > 2 * Real.pi ∧
    11 * thetaOne + 6 * thetaZero > 2 * Real.pi ∧
    9 * thetaTwo + 7 * thetaOne > 2 * Real.pi := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
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
