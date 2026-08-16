/- GID: D5/S3/Arith/Congruence/ModThreeNormObstruction
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/ModThreeNormObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A number 3m - 1 is not representable as x^2 + 3y^2 over the integers. -/

import D5.S1.Phase.ZeroOrbitCongruence
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.ModThreeNormObstruction

/-- No integer congruent to two modulo three is the norm `x ^ 2 + 3 * y ^ 2`.
This is the local norm obstruction used in the even branch of appendix E.52. -/
theorem three_mul_sub_one_not_quadratic_norm (m x y : ℤ) :
    x ^ 2 + 3 * y ^ 2 ≠ 3 * m - 1 := by
  intro h
  have hsq : (x : ZMod 3) ^ 2 = 0 ∨ (x : ZMod 3) ^ 2 = 1 := by
    simpa using
      D5.S1.Phase.ZeroOrbitCongruence.eisenstein_norm_mod_three (x : ZMod 3) 0
  have hz := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at hz
  have hthree : (3 : ZMod 3) = 0 := by decide
  simp only [hthree, zero_mul, add_zero, sub_eq_add_neg] at hz
  norm_num at hz
  rcases hsq with hzero | hone
  · have hne : (0 : ZMod 3) ≠ 2 := by decide
    exact hne (hzero.symm.trans hz)
  · have hne : (1 : ZMod 3) ≠ 2 := by decide
    exact hne (hone.symm.trans hz)

#print axioms three_mul_sub_one_not_quadratic_norm

end D5.S3.Arith.Congruence.ModThreeNormObstruction
