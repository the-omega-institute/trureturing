/- GID: D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct
   generality: I
   mirror-B: D5/B/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two mod-five sine determinants have golden ratio and discriminant product. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * D5 searches for fifth-angle sine products, their square-root value, and the
     corresponding golden ratio found no whole-statement owner.
   * The nearby massless holonomy module owns the general determinant-to-sine
     bridge, while the carrier module owns algebraic golden-ratio identities;
     neither states this pair of concrete sector identities.
   * Pinned Mathlib has no exact product theorem, but its exact fifth-angle
     identity `Real.cos_pi_div_five` is applied below together with
     `Real.sin_two_mul` and `Real.sin_sq_add_cos_sq`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.HolonomyDeterminant.DiscriminantDeterminantProduct

/-- The two mod-five observer-light sine determinants multiply to the square
root of five, while their ordered ratio is the golden ratio. -/
theorem discriminant_determinant_product :
    (2 * Real.sin (Real.pi / 5)) *
          (2 * Real.sin (2 * Real.pi / 5)) = Real.sqrt 5 ∧
      (2 * Real.sin (2 * Real.pi / 5)) /
          (2 * Real.sin (Real.pi / 5)) = Real.goldenRatio := by
  have hRootSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hSinSq := Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [Real.cos_pi_div_five] at hSinSq
  have hSinPos : 0 < Real.sin (Real.pi / 5) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos Real.pi_pos (by norm_num)
    · nlinarith [Real.pi_pos]
  constructor
  · rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
      Real.sin_two_mul, Real.cos_pi_div_five]
    nlinarith
  · apply (div_eq_iff (mul_ne_zero (by norm_num) hSinPos.ne')).2
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
      Real.sin_two_mul, Real.cos_pi_div_five]
    change 2 * (2 * Real.sin (Real.pi / 5) * ((1 + Real.sqrt 5) / 4)) =
      ((1 + Real.sqrt 5) / 2) * (2 * Real.sin (Real.pi / 5))
    ring

#print axioms discriminant_determinant_product

end D5.S3.Analytic.HolonomyDeterminant.DiscriminantDeterminantProduct
