/- GID: D5/S3/Factorization/MarkovEquationMutation
   generality: G
   mirror-B: D5/B/S3/Factorization/MarkovEquationMutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coordinate mutation preserves the cubic equation; classification remains unresolved. -/

import Mathlib.Tactic

namespace D5.S3.Factorization.MarkovEquationMutation

/-- The coordinate mutation that generates adjacent nodes of the integer solution tree preserves
the defining equation. The identity is freely valid over every commutative ring. -/
theorem markov_equation_mutation {R : Type*} [CommRing R] (x y z : R)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z) :
    x ^ 2 + y ^ 2 + (3 * x * y - z) ^ 2 =
      3 * x * y * (3 * x * y - z) := by
  calc
    x ^ 2 + y ^ 2 + (3 * x * y - z) ^ 2 =
        (x ^ 2 + y ^ 2 + z ^ 2) + 9 * x ^ 2 * y ^ 2 - 6 * x * y * z := by ring
    _ = 3 * x * y * z + 9 * x ^ 2 * y ^ 2 - 6 * x * y * z := by rw [h]
    _ = 3 * x * y * (3 * x * y - z) := by ring

end D5.S3.Factorization.MarkovEquationMutation
