/- GID: D5/S3/Geometry/Hyperideal/IndependentEndpointBarrier
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/IndependentEndpointBarrier
   mirror-E: none(waiver:independent-endpoint-certificate-obstruction)
   anchors: []
   utility: none
   digest: Independent opposite-edge endpoint certificates cannot close degree eight or nine stars. -/

import Mathlib
import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-! Independent opposite-edge endpoint certificates cannot close degree eight or nine stars. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.IndependentEndpointBarrier
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/- The one-variable endpoint obtained after lowering the opposite coordinate to one. -/
def endpointRatio (b : ℝ) : ℝ :=
  (2 * b ^ 3 + b ^ 2 + 1) / (2 * b ^ 3 + 3 * b ^ 2 - 1)

private theorem endpointRatio_den_pos (b : ℝ) (hb : 1 < b) :
    0 < 2 * b ^ 3 + 3 * b ^ 2 - 1 := by
  have hb0 : 0 < b := by linarith
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
  have hb3 : 0 < b ^ 3 := by positivity
  nlinarith

private theorem endpointRatio_lower_bound (b : ℝ) (hb : 1 < b) (hb2 : b ≤ 2) :
    7 / 9 ≤ endpointRatio b := by
  have hden : 0 < 2 * b ^ 3 + 3 * b ^ 2 - 1 := endpointRatio_den_pos b hb
  unfold endpointRatio
  apply (le_div_iff₀ hden).2
  have hpoly : 0 ≤ 4 * (b - 2) ^ 2 * (b + 1) := by positivity
  nlinarith [hpoly]

private theorem endpoint_cosine_formula (b : ℝ) (hb : 1 < b) :
    cosine b b b 1 b b = endpointRatio b := by
  have hrad : 0 ≤ rad b b b := by
    unfold rad
    have hb0 : 0 < b := by linarith
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
    have hb3 : 0 < b ^ 3 := by positivity
    nlinarith
  unfold cosine
  rw [div_div, ← pow_two, Real.sq_sqrt hrad]
  unfold numerator endpointRatio rad
  field_simp [endpointRatio_den_pos b hb]
  ring

private theorem endpoint_angle_lt_two_pi_div_nine (b : ℝ) (hb : 1 < b) (hb2 : b ≤ 2) :
    Real.arccos (cosine b b b 1 b b) < 2 * Real.pi / 9 := by
  rw [endpoint_cosine_formula b hb]
  have hcos : Real.cos (2 * Real.pi / 9) < 7 / 9 := by
    let x : ℝ := Real.cos (2 * Real.pi / 9)
    have hxle : x ≤ 1 := by
      dsimp [x]
      exact Real.cos_le_one _
    have hcontra : ¬ 7 / 9 ≤ x := by
      intro h
      have hfac : 0 < 4 * x ^ 2 + 4 * x * (7 / 9) + 4 * (7 / 9) ^ 2 - 3 := by
        nlinarith [sq_nonneg (x - 7 / 9)]
      have hprod : 0 ≤ (x - 7 / 9) *
          (4 * x ^ 2 + 4 * x * (7 / 9) + 4 * (7 / 9) ^ 2 - 3) :=
        mul_nonneg (by linarith) hfac.le
      have hpoly : (-(1 / 2 : ℝ)) < 4 * (7 / 9) ^ 3 - 3 * (7 / 9) := by
        norm_num
      have htriple : -(1 / 2 : ℝ) = 4 * x ^ 3 - 3 * x := by
        dsimp [x]
        have hangle : 3 * (2 * Real.pi / 9) = 2 * Real.pi / 3 := by ring
        have ht := Real.cos_three_mul (2 * Real.pi / 9)
        rw [hangle] at ht
        have htwo : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
          calc
            Real.cos (2 * Real.pi / 3) = Real.cos (2 * (Real.pi / 3)) := by
              congr 1 <;> ring
            _ = 2 * Real.cos (Real.pi / 3) ^ 2 - 1 := Real.cos_two_mul _
            _ = -(1 / 2 : ℝ) := by rw [Real.cos_pi_div_three]; norm_num
        rw [htwo] at ht
        exact ht
      nlinarith
    linarith
  have hratio : 7 / 9 ≤ endpointRatio b := endpointRatio_lower_bound b hb hb2
  have harccos : Real.arccos (endpointRatio b) ≤ Real.arccos (7 / 9) :=
    Real.arccos_le_arccos hratio
  have hangle : Real.arccos (7 / 9) < 2 * Real.pi / 9 := by
    have h := Real.arccos_lt_arccos (Real.neg_one_le_cos (2 * Real.pi / 9)) hcos
      (by norm_num : (7 / 9 : ℝ) ≤ 1)
    rw [Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])] at h
    exact h
  linarith

/- The exact local obstruction used by the degree-eight and degree-nine argument. -/
theorem independent_endpoint_certificate_fails
    (b : ℝ) (hb : 1 < b) (hb2 : b ≤ 2)
    (y z v w : ℝ)
    (hy1 : 1 ≤ y) (hy2 : y ≤ 2) (hyb : b ≤ y)
    (hz1 : 1 ≤ z) (hz2 : z ≤ 2) (hzb : b ≤ z)
    (hv1 : 1 ≤ v) (hv2 : v ≤ 2) (hvb : b ≤ v)
    (hw1 : 1 ≤ w) (hw2 : w ≤ 2) (hwb : b ≤ w) :
    let θ := Real.arccos (cosine b y z 1 v w)
    θ < 2 * Real.pi / 9 ∧ 8 * θ < 2 * Real.pi ∧ 9 * θ < 2 * Real.pi := by
  dsimp
  have hbase : cosine b b b 1 b b ≤ cosine b y z 1 v w := by
    apply cosine_mixed_comparison b b b 1 b b y z 1 v w
    · exact ⟨by linarith, hb2⟩
    · exact ⟨by linarith, hb2⟩
    · exact ⟨by linarith, hb2⟩
    · norm_num
    · exact ⟨by linarith, hb2⟩
    · exact ⟨by linarith, hb2⟩
    · exact ⟨hy1, hy2⟩
    · exact ⟨hz1, hz2⟩
    · norm_num
    · exact ⟨hv1, hv2⟩
    · exact ⟨hw1, hw2⟩
    · exact hyb
    · exact hzb
    · norm_num
    · exact hvb
    · exact hwb
  have hangle : Real.arccos (cosine b y z 1 v w) ≤
      Real.arccos (cosine b b b 1 b b) := by
    exact Real.arccos_le_arccos hbase
  have hbase_lt := endpoint_angle_lt_two_pi_div_nine b hb hb2
  have hθ : Real.arccos (cosine b y z 1 v w) < 2 * Real.pi / 9 :=
    lt_of_le_of_lt hangle hbase_lt
  refine ⟨hθ, ?_, ?_⟩ <;> nlinarith [Real.pi_pos]

#print axioms independent_endpoint_certificate_fails

end D5.S3.Geometry.Hyperideal.IndependentEndpointBarrier
