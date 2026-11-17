/- GID: D5/S3/QuantumChannels/ContractionGeometry/NorthPoleBallCriterion
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ContractionGeometry/NorthPoleBallCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An isotropic transverse scaling with axial drift fixing the north pole preserves the closed Euclidean unit ball exactly when its squared transverse factor is at most the axial factor. -/

import D5.S3.QuantumChannels.AmplitudeDampingContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion

open D5.S3.QuantumChannels.AmplitudeDampingContraction (dampedAxis)

/-- A transverse factor above the axial bound sends an explicit point of the unit sphere outside
the unit ball. The height deficit is positive and at most one, including at zero axial factor. -/
private theorem sphere_point_outside_of_sq_gt (a lambda : ℝ) (ha : 0 ≤ a)
    (h : a < lambda ^ 2) :
    ∃ x z : ℝ, x ^ 2 + z ^ 2 = 1 ∧
      1 < (lambda * x) ^ 2 + (dampedAxis (1 - a) z) ^ 2 := by
  let d : ℝ := (lambda ^ 2 - a) / (lambda ^ 2 + 1)
  have hb : 0 < lambda ^ 2 + 1 := by positivity
  have hd : 0 < d := div_pos (sub_pos.mpr h) hb
  have hd1 : d ≤ 1 := (div_le_one hb).2 (by linarith)
  have hdeq : d * (lambda ^ 2 + 1) = lambda ^ 2 - a :=
    div_mul_cancel₀ _ (ne_of_gt hb)
  have hs : 0 ≤ d * (2 - d) := mul_nonneg hd.le (by linarith)
  have hx : (Real.sqrt (d * (2 - d))) ^ 2 = d * (2 - d) := Real.sq_sqrt hs
  have hbracket : 0 < 2 * (lambda ^ 2 - a) - d * (lambda ^ 2 - a ^ 2) := by
    have hsmall : d * (lambda ^ 2 - a ^ 2) ≤ lambda ^ 2 - a := by
      nlinarith only [hdeq, mul_nonneg hd.le (sq_nonneg a), hd.le]
    linarith
  refine ⟨Real.sqrt (d * (2 - d)), 1 - d, ?_, ?_⟩
  · nlinarith only [hx]
  · have hexcess := mul_pos hd hbracket
    dsimp only [dampedAxis]
    nlinarith only [hx, hexcess]

/-- For `0 ≤ a ≤ 1`, the map `(x,y,z) ↦ (lambda*x,lambda*y,a*z+1-a)` preserves
the whole closed Euclidean unit ball if and only if `lambda² ≤ a`. The axial expression reuses
the amplitude-damping coordinate with `gamma = 1-a`; the transverse factor may have either sign. -/
theorem north_pole_ball_preserving_iff (a lambda : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 →
      (lambda * x) ^ 2 + (lambda * y) ^ 2 + (dampedAxis (1 - a) z) ^ 2 ≤ 1) ↔
      lambda ^ 2 ≤ a := by
  constructor
  · intro hball
    by_contra h
    obtain ⟨x, z, hsphere, hout⟩ := sphere_point_outside_of_sq_gt a lambda ha0 (lt_of_not_ge h)
    have hin := hball x 0 z (by simpa using hsphere.le)
    norm_num only [mul_zero, zero_pow, add_zero] at hin
    exact (not_lt_of_ge hin) hout
  · intro hbound x y z hball
    have htrans : lambda ^ 2 * (x ^ 2 + y ^ 2) ≤ a * (x ^ 2 + y ^ 2) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    have hinput : a * (x ^ 2 + y ^ 2) ≤ a * (1 - z ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) ha0
    have hdefect : 0 ≤ a * (1 - a) * (1 - z) ^ 2 :=
      mul_nonneg (mul_nonneg ha0 (sub_nonneg.mpr ha1)) (sq_nonneg _)
    dsimp only [dampedAxis]
    nlinarith only [htrans, hinput, hdefect]

end D5.S3.QuantumChannels.ContractionGeometry.NorthPoleBallCriterion
