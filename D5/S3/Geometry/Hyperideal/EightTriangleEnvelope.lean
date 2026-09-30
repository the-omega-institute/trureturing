/- GID: D5/S3/Geometry/Hyperideal/EightTriangleEnvelope
   utility: none
   digest: Exact rational squared margins for the adjacent degree-eight
   three-star, three-cycle, and four-cycle endpoint envelopes.
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.EightTriangleEnvelope

/-- Lower-face squared margins for the three local packets. -/
theorem star_lower_sq : (73 : ℝ)^2 / 100^2 > 1 / 2 := by norm_num
theorem triangle_lower_sq : (8 : ℝ)^2 * 6 / 27^2 > 1 / 2 := by norm_num
theorem four_cycle_lower_sq : (293 : ℝ)^2 / 400^2 > 1 / 2 := by norm_num

/-- Upper-face squared margins for the three local packets. -/
theorem star_upper_sq : (121 : ℝ)^2 / 175^2 < 1 / 2 := by norm_num
theorem triangle_upper_sq : (13 : ℝ)^2 * 41 / 123^2 < 1 / 2 := by norm_num
theorem four_cycle_upper_sq : (473 : ℝ)^2 / 700^2 < 1 / 2 := by norm_num

/-- The high-edge endpoint margin used at the degree-sixteen threshold. -/
theorem high_upper_sq : (23 : ℝ)^2 / 25^2 < (2 + Real.sqrt 2) / 4 := by
  have hs : (0 : ℝ) <= Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := by norm_num
  nlinarith

#print axioms star_lower_sq
#print axioms triangle_lower_sq
#print axioms four_cycle_lower_sq
#print axioms star_upper_sq
#print axioms triangle_upper_sq
#print axioms four_cycle_upper_sq
#print axioms high_upper_sq

end D5.S3.Geometry.Hyperideal.EightTriangleEnvelope
