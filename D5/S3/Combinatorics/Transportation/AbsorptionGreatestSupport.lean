/- GID: D5/S3/Combinatorics/Transportation/AbsorptionGreatestSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/AbsorptionGreatestSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero absorption is equivalent to universal greatest support in finite additive-observation fibers over conical commutative coefficients. -/

import OmegaMath.Algebra.Refinement.AbsorptionGreatestSupport

set_option autoImplicit false

namespace D5.S3.Combinatorics.Transportation.AbsorptionGreatestSupport

universe u

/-- Original-coefficient absorption exactly characterizes the universal event. -/
theorem result (K : Type u) [AddCommMonoid K]
    (hc : ∀ x y : K, x + y = 0 → x = 0 ∧ y = 0) :
    (∀ x : K, x ≠ 0 → ∃ e : K, e ≠ 0 ∧ x + e = x) ↔
      (∀ (n : ℕ) (T : Type u) [AddMonoid T]
        (F : (Fin n → K) →+ T) (p : Fin n → K),
        ∃ r : Fin n → K, F r = F p ∧
          ∀ q : Fin n → K, F q = F p → ∀ i : Fin n, q i ≠ 0 → r i ≠ 0) :=
  Omega.Refinement.Absorption.absorption_iff_universal_greatest_support hc

end D5.S3.Combinatorics.Transportation.AbsorptionGreatestSupport
