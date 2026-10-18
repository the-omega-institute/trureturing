/- GID: D5/S3/Geometry/Hyperideal/CriticalBudgetInterval
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CriticalBudgetInterval
   mirror-E: none(waiver:parameterized-continuous-angle-budget)
   anchors: []
   utility: none
   digest: Exact opposite-edge lower-bound interval for the four-plus-two angle budget. -/

import D5.S3.Geometry.Hyperideal.CriticalTransitionStar
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.CriticalBudgetInterval
open D5.S3.Geometry.Hyperideal.CriticalTransitionStar
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

def oppositeThreshold : ℝ :=
  (25 - 33 * Real.sqrt ((1 - 49 / Real.sqrt 6534) / 2)) / 8

/-- The two prescribed six-occurrence face budgets are simultaneously strict
exactly above the opposite-edge threshold within the stated parameter range. -/
theorem exact_budget_interval (a : ℝ) (ha : 1 < a) (hb : a < 7 / 5) :
    cosine 2 (5/4) (5/4) a (5/4) (5/4) = (25-8*a)/33 ∧
    ((0 < 2*Real.pi - 6*Real.arccos (2*(2-a)/(a+1)) ∧
      0 < 4*Real.arccos (cosine 2 (5/4) (5/4) a (5/4) (5/4)) +
        2*beta - 2*Real.pi) ↔
    oppositeThreshold < a ∧ a < 7 / 5) := by
  have hendpoint : cosine 2 (5/4) (5/4) a (5/4) (5/4) = (25-8*a)/33 := by
    have hA : rad 2 (5/4) (5/4) = (99:ℝ)/8 := by norm_num [rad]
    have hP : numerator 2 (5/4) (5/4) a (5/4) (5/4) = 3*(25-8*a)/8 := by
      norm_num [numerator]; ring
    rw [cosine, hA, hP, div_div, ← pow_two,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 99/8)]
    ring
  refine ⟨hendpoint, ?_⟩
  rw [hendpoint]
  let q : ℝ := 49 / Real.sqrt 6534
  let v : ℝ := (25 - 8*a)/33
  let r : ℝ := Real.sqrt ((1-q)/2)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqsq : q^2 = (2401:ℝ)/6534 := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6534)]
    norm_num
  have hqone : q < 1 := by nlinarith
  have hvpos : 0 < v := by dsimp [v]; linarith
  have hvone : v < 1 := by dsimp [v]; linarith
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hradicand : 0 ≤ (1-q)/2 := by linarith
  have hrsq : r^2 = (1-q)/2 := by
    dsimp [r]
    exact Real.sq_sqrt hradicand
  have hbetaPos : 0 < beta := by
    change 0 < Real.arccos q
    exact Real.arccos_pos.mpr hqone
  have hbetaHalf : beta < Real.pi/2 := by
    change Real.arccos q < Real.pi/2
    exact Real.arccos_lt_pi_div_two.mpr hqpos
  have hvAnglePos : 0 < Real.arccos v := Real.arccos_pos.mpr hvone
  have hvAngleHalf : Real.arccos v < Real.pi/2 :=
    Real.arccos_lt_pi_div_two.mpr hvpos
  have hcosTwo : Real.cos (2*Real.arccos v) = 2*v^2-1 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith) hvone.le]
  have hcosBeta : Real.cos (Real.pi-beta) = -q := by
    change Real.cos (Real.pi-Real.arccos q) = -q
    rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) hqone.le]
  have hangle :
      (Real.pi-beta < 2*Real.arccos v) ↔ (2*v^2-1 < -q) := by
    constructor
    · intro hh
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
        (show 0 ≤ Real.pi-beta by linarith [Real.pi_pos])
        (show 2*Real.arccos v ≤ Real.pi by linarith) hh
      rw [hcosTwo, hcosBeta] at hc
      exact hc
    · intro hh
      by_contra hn
      have hle : 2*Real.arccos v ≤ Real.pi-beta := le_of_not_gt hn
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ 2*Real.arccos v by linarith)
        (show Real.pi-beta ≤ Real.pi by linarith) hle
      rw [hcosTwo, hcosBeta] at hc
      linarith
  have hthreshold : oppositeThreshold = (25-33*r)/8 := rfl
  have hroot : (2*v^2-1 < -q) ↔ oppositeThreshold < a := by
    constructor
    · intro hh
      have hvr : v < r := by nlinarith
      rw [hthreshold]
      dsimp [v] at hvr
      linarith
    · intro hh
      rw [hthreshold] at hh
      have hvr : v < r := by dsimp [v]; linarith
      have hprod : 0 < (r-v)*(r+v) :=
        mul_pos (sub_pos.mpr hvr) (by linarith)
      nlinarith
  have hden : 0 < a+1 := by linarith
  have hlowCos : (1/2:ℝ) < 2*(2-a)/(a+1) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hlowCosOne : 2*(2-a)/(a+1) ≤ (1:ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have hhalf : Real.arccos (1/2:ℝ) = Real.pi/3 := by
    rw [← Real.cos_pi_div_three,
      Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  have hlowAngle : Real.arccos (2*(2-a)/(a+1)) < Real.pi/3 := by
    have hh := Real.arccos_lt_arccos
      (by norm_num : (-1:ℝ) ≤ 1/2) hlowCos hlowCosOne
    rw [hhalf] at hh
    exact hh
  have hlower : 0 < 2*Real.pi - 6*Real.arccos (2*(2-a)/(a+1)) := by
    linarith
  constructor
  · intro hh
    have hang : Real.pi-beta < 2*Real.arccos v := by
      dsimp [v]
      linarith [hh.2]
    exact ⟨hroot.mp (hangle.mp hang), hb⟩
  · intro hh
    have hang := hangle.mpr (hroot.mpr hh.1)
    constructor
    · exact hlower
    · dsimp [v] at hang
      linarith

#print axioms exact_budget_interval
end D5.S3.Geometry.Hyperideal.CriticalBudgetInterval
