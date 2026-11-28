/- GID: D5/S3/Combinatorics/Transportation/GroupGreatestSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/GroupGreatestSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Torsion-freeness is equivalent to universal greatest support in finite additive-observation fibers of an abelian group. -/

import D5.S3.Algebra.Refinement.GroupGreatestSupport

set_option autoImplicit false

namespace D5.S3.Combinatorics.Transportation.GroupGreatestSupport

universe u

/-- The exact group-coefficient event, with positive natural scalar multiples,
all finite powers, and arbitrary additive-monoid targets in the same universe. -/
theorem result (G : Type u) [AddCommGroup G] :
    (∀ k : ℕ, 0 < k → ∀ x : G, k • x = 0 → x = 0) ↔
      ∀ (n : ℕ) (T : Type u) [AddMonoid T]
        (F : (Fin n → G) →+ T) (p : Fin n → G),
        ∃ r : Fin n → G, F r = F p ∧
          ∀ q : Fin n → G, F q = F p → ∀ i : Fin n, q i ≠ 0 → r i ≠ 0 :=
  Omega.Refinement.GroupSupport.torsion_free_iff_universal_greatest_support G

end D5.S3.Combinatorics.Transportation.GroupGreatestSupport
