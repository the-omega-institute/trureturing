/- GID: D5/S3/Factorization/UnimodularMonomialSubstitution
   generality: G
   mirror-B: D5/B/S3/Factorization/UnimodularMonomialSubstitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The determinant-one monomial substitution has an explicit inverse on nonzero pairs. -/

import Mathlib

namespace D5.S3.Factorization.UnimodularMonomialSubstitution

/-- The substitution `(u, v) -> (u^2 / v, v^2 / u^3)` is inverted by
`(P, Q) -> (P^2 * Q, P^3 * Q^2)` away from the coordinate axes. -/
theorem unimodular_monomial_substitution (u v : Complex)
    (hu : Not (u = 0)) (hv : Not (v = 0)) :
    let P := u ^ 2 / v
    let Q := v ^ 2 / u ^ 3
    And (P ^ 2 * Q = u) (P ^ 3 * Q ^ 2 = v) := by
  dsimp
  constructor <;> field_simp

/-- The nonzero domain of the substitution is inhabited. -/
example : Exists fun u : Complex => Exists fun v : Complex =>
    And (Not (u = 0)) (Not (v = 0)) := by
  exact Exists.intro 2 (Exists.intro 3 (And.intro (by norm_num) (by norm_num)))

end D5.S3.Factorization.UnimodularMonomialSubstitution
