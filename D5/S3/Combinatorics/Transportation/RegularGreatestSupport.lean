/- GID: D5/S3/Combinatorics/Transportation/RegularGreatestSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/RegularGreatestSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every joint additive-observation fiber over a finite power of a conical regular commutative monoid has greatest support. -/

import D5.S3.Algebra.Refinement.RegularGreatestSupport

set_option autoImplicit false

namespace D5.S3.Combinatorics.Transportation.RegularGreatestSupport

open Omega.Refinement Omega.Refinement.Regular

universe u v w z

/-- The greatest-support event, with the original coefficient operations,
empty finite carriers, and arbitrary dependent additive observations. -/
theorem result (K : Type u) [AddCommMonoid K]
    (hc : ∀ x y : K, x + y = 0 → x = 0 ∧ y = 0)
    (hr : ∀ x : K, ∃ y : K, x + y + x = x)
    (I : Type v) [Finite I] (J : Type w) (M : J → Type z)
    [∀ j, AddMonoid (M j)] (F : ∀ j, (I → K) →+ M j) (p : I → K) :
    ∃ r : I → K, (∀ j, F j r = F j p) ∧
      ∀ q : I → K, (∀ j, F j q = F j p) →
        ∀ i : I, q i ≠ 0 → r i ≠ 0 :=
  exists_greatest_joint_fiber_support hc hr F p

end D5.S3.Combinatorics.Transportation.RegularGreatestSupport
