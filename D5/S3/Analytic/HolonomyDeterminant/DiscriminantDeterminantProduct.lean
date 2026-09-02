/- GID: D5/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct
   generality: G
   mirror-B: D5/B/S3/Analytic/HolonomyDeterminant/DiscriminantDeterminantProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional Lerch data give the two mod-five holonomy determinant identities. -/

import D5.S3.Analytic.HolonomyDeterminant.MasslessHolonomyDeterminant
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * D5 searches for the two massless holonomy determinant values, their product,
     and their ratio found no whole-statement owner.
   * `MasslessHolonomyDeterminant.massless_holonomy_determinant` owns the conditional
     determinant-to-sine bridge and is applied at both mod-five representatives.
   * Pinned Mathlib has no exact product theorem, but its exact fifth-angle
     identity `Real.cos_pi_div_five` is applied below together with
     `Real.sin_two_mul` and `Real.sin_sq_add_cos_sq`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.HolonomyDeterminant.DiscriminantDeterminantProduct

open D5.S3.Analytic.HolonomyDeterminant.MasslessHolonomyDeterminant

/-- Conditional reflected-Hurwitz data identify the two mod-five observer-light
sector determinants: their product is the square root of five, and the ordered
second-to-first ratio is the golden ratio. -/
theorem discriminant_determinant_product
    (hLerchOne : HasReflectedHurwitzDerivativeAtZeroFormula (1 / 5 : Real))
    (hLerchTwo : HasReflectedHurwitzDerivativeAtZeroFormula (2 / 5 : Real)) :
    masslessHolonomyDeterminant (1 / 5) *
          masslessHolonomyDeterminant (2 / 5) = (Real.sqrt 5 : Complex) ∧
      masslessHolonomyDeterminant (2 / 5) /
          masslessHolonomyDeterminant (1 / 5) = (Real.goldenRatio : Complex) := by
  have hDetOne := massless_holonomy_determinant (1 / 5 : Real)
    (by norm_num : (1 / 5 : Real) ∈ Set.Ioo 0 1) hLerchOne
  have hDetTwo := massless_holonomy_determinant (2 / 5 : Real)
    (by norm_num : (2 / 5 : Real) ∈ Set.Ioo 0 1) hLerchTwo
  have hTrig :
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
  constructor
  · rw [hDetOne, hDetTwo]
    norm_cast
    convert hTrig.1 using 1
    all_goals ring_nf
  · rw [hDetOne, hDetTwo]
    norm_cast
    convert hTrig.2 using 1
    all_goals ring_nf

#print axioms discriminant_determinant_product

end D5.S3.Analytic.HolonomyDeterminant.DiscriminantDeterminantProduct
