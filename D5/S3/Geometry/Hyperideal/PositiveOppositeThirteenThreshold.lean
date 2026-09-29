/- GID: D5/S3/Geometry/Hyperideal/PositiveOppositeThirteenThreshold
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/PositiveOppositeThirteenThreshold
   mirror-E: none(waiver:positive-opposite-thirteen-threshold)
   anchors: []
   utility: none
   digest: The specified positive-opposite-bound scheme first works at degree thirteen. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.PositiveOppositeThirteenThreshold

def lowBound (a : ℝ) : ℝ := 2 * (2-a) / (a+1)

def criticalUpper (a b : ℝ) : ℝ := (2*b^2-a) / (1+2*b^2)

def highUpper (b : ℝ) : ℝ := (b^3-b^2+8*b+1) / (3*(2*b^2+1))

/-- For the prescribed common lower and upper bounds, thirteen is the first
high-edge degree satisfying the three strict endpoint cosine inequalities. -/
theorem exact_positive_opposite_thirteen_threshold :
    (∀ (D : ℕ), 6 < D → D ≤ 12 → ∀ a b : ℝ,
      1 < a → a < 2 → 1 < b → b < 2 →
      ¬ (Real.cos (2*Real.pi/6) < lowBound a ∧
         criticalUpper a b < Real.cos (2*Real.pi/6) ∧
         highUpper b < Real.cos (2*Real.pi/D))) ∧
    (∃ a b : ℝ, 1 < a ∧ a < 2 ∧ 1 < b ∧ b < 2 ∧
      Real.cos (2*Real.pi/6) < lowBound a ∧
      criticalUpper a b < Real.cos (2*Real.pi/6) ∧
      highUpper b < Real.cos (2*Real.pi/13)) := by
  have hcos6 : Real.cos (2*Real.pi/6) = (1/2 : ℝ) := by
    rw [show 2*Real.pi/6 = Real.pi/3 by ring, Real.cos_pi_div_three]
  constructor
  · intro D hD6 hD12 a b ha1 _ha2 hb1 _hb2 ⟨hL, hU, hH⟩
    rw [hcos6] at hL hU
    have hdenL : 0 < a+1 := by linarith
    have ha75 : a < 7/5 := by
      unfold lowBound at hL
      rw [lt_div_iff₀ hdenL] at hL
      nlinarith
    have hdenU : 0 < 1+2*b^2 := by nlinarith [sq_nonneg b]
    have hbSq : b^2 < 19/10 := by
      unfold criticalUpper at hU
      rw [div_lt_iff₀ hdenU] at hU
      nlinarith
    have hb75 : b < 7/5 := by
      by_contra h
      have hbge : (7/5 : ℝ) ≤ b := le_of_not_gt h
      nlinarith [sq_nonneg (b-7/5)]
    have hquad : 41*b^2-200*b+48 < 0 := by
      have hmul : 0 < b*(7/5-b) := mul_pos (by linarith) (by linarith)
      nlinarith
    have hprod : 0 < (5*b-7)*(41*b^2-200*b+48) :=
      mul_pos_of_neg_of_neg (by linarith) hquad
    have hdenH : 0 < 3*(2*b^2+1) := by nlinarith [sq_nonneg b]
    have hHlower : (541/615 : ℝ) < highUpper b := by
      unfold highUpper
      rw [lt_div_iff₀ hdenH]
      nlinarith [hprod]
    have hsqrt : Real.sqrt 3 / 2 < (541/615 : ℝ) := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      have hnonneg := Real.sqrt_nonneg (3 : ℝ)
      nlinarith
    have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
    have hDlow : (6 : ℝ) < D := by exact_mod_cast hD6
    have hDhigh : (D : ℝ) ≤ 12 := by exact_mod_cast hD12
    have hangleLow : Real.pi/6 ≤ 2*Real.pi/D := by
      apply (le_div_iff₀ hDpos).2
      nlinarith [Real.pi_pos]
    have hangleHigh : 2*Real.pi/D ≤ Real.pi := by
      apply (div_le_iff₀ hDpos).2
      nlinarith [Real.pi_pos]
    have hcosD : Real.cos (2*Real.pi/D) ≤ Real.cos (Real.pi/6) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hangleHigh hangleLow
    rw [Real.cos_pi_div_six] at hcosD
    linarith
  · refine ⟨1399/1000, 689/500, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_, ?_, ?_⟩
    · rw [hcos6]
      norm_num [lowBound]
    · rw [hcos6]
      norm_num [criticalUpper]
    · have hvalue : highUpper (689/500 : ℝ) = 176969141/199907000 := by
        norm_num [highUpper]
      rw [hvalue]
      have hpi : Real.pi < (22/7 : ℝ) := by
        have h := Real.pi_lt_d4
        norm_num at h ⊢
        linarith
      have hangle : 2*Real.pi/13 < (44/91 : ℝ) := by
        nlinarith
      have hcos : (176969141/199907000 : ℝ) < Real.cos (44/91 : ℝ) := by
        let r : ℝ := 44/91
        let y : ℝ := r/2
        have hy : |y| ≤ 1 := by dsimp [y, r]; norm_num
        have hsin := Real.sin_bound hy
        have hsinUpper : Real.sin y ≤ y-y^3/6+|y|^5/100 := by
          have hh := (abs_sub_le_iff.mp hsin).1
          linarith
        have hsinNonneg : 0 ≤ Real.sin y := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          · dsimp [y, r]; norm_num
          · dsimp [y, r]; nlinarith [Real.pi_gt_three]
        have hnumeric : 0 < y-y^3/6+|y|^5/100 := by
          dsimp [y, r]
          norm_num
        have hsq : Real.sin y ^ 2 ≤ (y-y^3/6+|y|^5/100)^2 := by
          have hp := mul_nonneg (sub_nonneg.mpr hsinUpper)
            (add_nonneg hnumeric.le hsinNonneg)
          nlinarith
        have hcosEq : Real.cos r = 1 - 2 * Real.sin y ^ 2 := by
          have hr : 2*y = r := by dsimp [y]; ring
          rw [← hr, Real.cos_two_mul_eq_one_sub]
        rw [show (44/91 : ℝ) = r by rfl, hcosEq]
        have hn : (176969141/199907000 : ℝ) <
            1 - 2*(y-y^3/6+|y|^5/100)^2 := by
          dsimp [y, r]
          norm_num
        nlinarith
      have hcosMono : Real.cos (44/91 : ℝ) ≤ Real.cos (2*Real.pi/13) := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
          (by norm_num; nlinarith [Real.pi_gt_three]) hangle.le
      linarith

#print axioms exact_positive_opposite_thirteen_threshold

end D5.S3.Geometry.Hyperideal.PositiveOppositeThirteenThreshold
