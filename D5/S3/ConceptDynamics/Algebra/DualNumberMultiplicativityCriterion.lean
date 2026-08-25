/- GID: D5/S3/ConceptDynamics/Algebra/DualNumberMultiplicativityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Algebra/DualNumberMultiplicativityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical dual-number lift is multiplicative exactly under the product rule. -/

import Mathlib.Algebra.DualNumber

/- Library-search audit trail (2026-08-25):
   * Repository searches for dual numbers, square-zero extensions, and the
     product rule found no theorem with the public equivalence below.
   * Pinned Mathlib provides `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`,
     `TrivSqZeroExt.ext`, and `DualNumber.snd_mul`; these canonical primitives
     are used directly instead of introducing another lift definition.
   * Generic `LinearMap.map_mul_iff` describes multiplication preservation as
     an equality of bilinear maps, but does not identify its condition with
     the displayed product rule for this dual-number lift.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Algebra.DualNumberMultiplicativityCriterion

open TrivSqZeroExt

/-- The canonical map `a |-> inl a + inr (D a)` into the dual numbers preserves
multiplication exactly when the linear map `D` satisfies the product rule. -/
theorem dual_number_lift_preserves_mul_iff_product_rule
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (D : A →ₗ[R] A) :
    (∀ a b : A,
      (inl (a * b) + inr (D (a * b)) : DualNumber A) =
        (inl a + inr (D a)) * (inl b + inr (D b))) ↔
      ∀ a b : A, D (a * b) = a * D b + D a * b := by
  constructor
  · intro h a b
    have hSecond := congrArg (TrivSqZeroExt.snd (R := A) (M := A)) (h a b)
    simpa using hSecond
  · intro h a b
    apply TrivSqZeroExt.ext
    · simp
    · simp [h]

#print axioms dual_number_lift_preserves_mul_iff_product_rule

end D5.S3.ConceptDynamics.Algebra.DualNumberMultiplicativityCriterion
