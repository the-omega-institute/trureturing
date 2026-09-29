/- GID: D5/S3/Geometry/Hyperideal/TwoLayerNineteenThreshold
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/TwoLayerNineteenThreshold
   mirror-E: none(waiver:uniform-two-layer-angle-obstruction)
   anchors: []
   utility: none
   digest: The uniform two-layer angle scheme cannot work below degree nineteen. -/

import Mathlib
import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.TwoLayerNineteenThreshold
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- The low-edge endpoint cosine in the uniform two-layer scheme. -/
def lowCos (b c : ℝ) : ℝ := (2*c^2-b+1)/(2*c^2+b-1)

/-- The high-edge worst-case endpoint cosine in the same scheme. -/
def highCos (b c : ℝ) : ℝ := (2*b^2-c+1)/(2*b^2+c-1)

/-- For the prescribed uniform two-layer endpoint estimates, a low-edge angle
strictly above pi/3 excludes a high-edge angle strictly above 2pi/D when D ≤ 18. -/
private theorem no_uniform_two_layer_below_nineteen
    (D : ℕ) (hDpos : 0 < D) (hD18 : D ≤ 18)
    (b c : ℝ) (hb1 : 1 < b) (hb2 : b ≤ 2) (hc1 : 1 < c) (_hcb : c ≤ b) :
    ¬ (Real.pi / 3 < Real.arccos (cosine b c c 1 c c) ∧
       2 * Real.pi / D < Real.arccos (cosine c b b 1 b b)) := by
  have hEndpoint : ∀ x y : ℝ, 1 < x → 1 < y →
      cosine x y y 1 y y = (2*y^2-x+1)/(2*y^2+x-1) := by
    intro x y hx hy
    have hrad : 0 ≤ rad x y y := by
      unfold rad
      nlinarith [sq_nonneg x, sq_nonneg y,
        mul_pos (show 0 < x by linarith) (sq_pos_of_pos (by linarith : 0 < y))]
    have hx0 : x + 1 ≠ 0 := by linarith
    have hd0 : 2*y^2+x-1 ≠ 0 := by nlinarith [sq_nonneg y]
    have hradFactor : rad x y y = (x+1)*(2*y^2+x-1) := by
      unfold rad
      ring
    have hnumFactor : numerator x y y 1 y y = (x+1)*(2*y^2-x+1) := by
      unfold numerator
      ring
    unfold cosine
    rw [div_div, ← pow_two, Real.sq_sqrt hrad, hradFactor, hnumFactor]
    field_simp
  intro ⟨hLowAngle, hHighAngle⟩
  have hLowEndpoint : cosine b c c 1 c c = lowCos b c := by
    simpa only [lowCos] using hEndpoint b c hb1 hc1
  have hHighEndpoint : cosine c b b 1 b b = highCos b c := by
    simpa only [highCos] using hEndpoint c b hc1 hb1
  rw [hLowEndpoint] at hLowAngle
  rw [hHighEndpoint] at hHighAngle
  have hLowCos : lowCos b c < 1/2 := by
    by_contra h
    have hh : (1/2 : ℝ) ≤ lowCos b c := le_of_not_gt h
    have hle := Real.arccos_le_arccos hh
    have hangle : Real.arccos (1/2 : ℝ) = Real.pi / 3 := by
      rw [← Real.cos_pi_div_three]
      exact Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
    rw [hangle] at hle
    linarith
  have hHighCos : (47/50 : ℝ) < highCos b c := by
    have hdenLow : 0 < 2*c^2+b-1 := by nlinarith [sq_nonneg c]
    have hLow' : 2*c^2 < 3*(b-1) := by
      unfold lowCos at hLowCos
      rw [div_lt_iff₀ hdenLow] at hLowCos
      nlinarith
    have hb53 : 5/3 < b := by nlinarith [sq_nonneg (c-1)]
    have hRatio : 97*(c-1) < 6*b^2 := by
      by_cases hb : b ≤ 39/20
      · have hV : 4*(c-1) < 3*b-5 := by
          nlinarith [mul_pos (sub_pos.mpr hc1) (show 0 < c-1 by linarith)]
        have hq : 0 ≤ 24*b^2-291*b+485 := by
          have ha : 0 ≤ (39/20-b)*(291-24*(b+39/20)) := by
            apply mul_nonneg
            · linarith
            · linarith
          nlinarith
        nlinarith
      · have hb' : 39/20 < b := lt_of_not_ge hb
        have hc49 : c < 49/40 := by nlinarith [sq_nonneg (c-49/40)]
        nlinarith [sq_nonneg (b-39/20)]
    have hdenHigh : 0 < 2*b^2+c-1 := by nlinarith [sq_nonneg b]
    unfold highCos
    rw [lt_div_iff₀ hdenHigh]
    nlinarith
  have hCosNinth : Real.cos (Real.pi / 9) < 47 / 50 := by
    let x : ℝ := Real.cos (Real.pi / 9)
    have hxle : x ≤ 1 := by
      dsimp [x]
      exact Real.cos_le_one _
    have hcontra : ¬ 47/50 ≤ x := by
      intro h
      have hfac : 0 < 4*x^2 + 4*x*(47/50) + 4*(47/50)^2 - 3 := by
        nlinarith [sq_nonneg (x - 47/50)]
      have hprod : 0 ≤ (x - 47/50) *
          (4*x^2 + 4*x*(47/50) + 4*(47/50)^2 - 3) :=
        mul_nonneg (by linarith) (le_of_lt hfac)
      have hpoly : (1/2 : ℝ) < 4*(47/50)^3 - 3*(47/50) := by norm_num
      have htriple : 1/2 = 4*x^3 - 3*x := by
        dsimp [x]
        have hangle : 3 * (Real.pi / 9) = Real.pi / 3 := by ring
        have ht := Real.cos_three_mul (Real.pi / 9)
        rw [hangle, Real.cos_pi_div_three] at ht
        exact ht
      nlinarith
    linarith
  have hNinth : Real.arccos (47/50 : ℝ) < Real.pi / 9 := by
    have h := Real.arccos_lt_arccos (Real.neg_one_le_cos _)
      hCosNinth (by norm_num : (47/50 : ℝ) ≤ 1)
    rw [Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])] at h
    exact h
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hDpos
  have hBound : Real.pi / 9 ≤ 2 * Real.pi / D := by
    apply (le_div_iff₀ hDreal).2
    have hDreal18 : (D : ℝ) ≤ 18 := by exact_mod_cast hD18
    nlinarith [Real.pi_pos]
  have hArccos : Real.arccos (highCos b c) ≤ Real.arccos (47/50 : ℝ) :=
    Real.arccos_le_arccos hHighCos.le
  linarith

/-- Nineteen is the exact first degree at which both prescribed strict
uniform two-layer endpoint angle bounds can hold. -/
theorem exact_uniform_two_layer_threshold :
    (∀ (D : ℕ), 0 < D → D ≤ 18 → ∀ b c : ℝ,
      1 < b → b ≤ 2 → 1 < c → c ≤ b →
      ¬ (Real.pi / 3 < Real.arccos (cosine b c c 1 c c) ∧
         2 * Real.pi / D < Real.arccos (cosine c b b 1 b b))) ∧
    (∃ b c : ℝ, 1 < b ∧ b ≤ 2 ∧ 1 < c ∧ c ≤ b ∧
      Real.pi / 3 < Real.arccos (cosine b c c 1 c c) ∧
      2 * Real.pi / 19 < Real.arccos (cosine c b b 1 b b)) := by
  constructor
  · intro D hDpos hD18 b c hb1 hb2 hc1 hcb
    exact no_uniform_two_layer_below_nineteen D hDpos hD18 b c hb1 hb2 hc1 hcb
  · refine ⟨2, 153/125, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · have hEndpoint : cosine 2 (153/125) (153/125) 1 (153/125) (153/125) =
          (31193/62443 : ℝ) := by
        unfold cosine
        rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num [rad])]
        norm_num [numerator, rad]
      rw [hEndpoint]
      have h := Real.arccos_lt_arccos
        (by norm_num : (-1 : ℝ) ≤ 31193/62443)
        (by norm_num : (31193/62443 : ℝ) < 1/2)
        (by norm_num : (1/2 : ℝ) ≤ 1)
      have hhalf : Real.arccos (1/2 : ℝ) = Real.pi / 3 := by
        rw [← Real.cos_pi_div_three]
        exact Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
      rwa [hhalf] at h
    · have hEndpoint : cosine (153/125) 2 2 1 2 2 = (243/257 : ℝ) := by
        unfold cosine
        rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num [rad])]
        norm_num [numerator, rad]
      rw [hEndpoint]
      have hpi : Real.pi < (31416/10000 : ℝ) := by
        convert Real.pi_lt_d4 using 1
        norm_num
      have hhalf : 2 * Real.pi / 19 < (44/133 : ℝ) := by
        nlinarith
      have hcos : (243/257 : ℝ) < Real.cos (44/133 : ℝ) := by
        let r : ℝ := 44/133
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
        rw [show (44/133 : ℝ) = r by rfl, hcosEq]
        have hn : (243/257 : ℝ) < 1 - 2*(y-y^3/6+|y|^5/100)^2 := by
          dsimp [y, r]
          norm_num
        nlinarith
      have hAngle := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 243/257)
        hcos (Real.cos_le_one _)
      rw [Real.arccos_cos (by norm_num) (by nlinarith [Real.pi_gt_three])] at hAngle
      linarith

#print axioms exact_uniform_two_layer_threshold

end D5.S3.Geometry.Hyperideal.TwoLayerNineteenThreshold
