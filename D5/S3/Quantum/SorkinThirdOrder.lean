/- GID: D5/S3/Quantum/SorkinThirdOrder
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The third-order inclusion-exclusion term vanishes for a quadratic amplitude weight. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.SorkinThirdOrder

variable {α R : Type*} [CommRing R] [StarRing R]

/-- The quadratic weight of a finite branch family over a commutative star ring. -/
def amplitudeWeight (v : α → R) (A : Finset α) : R :=
  (∑ a in A, v a) * star (∑ a in A, v a)

/-- Quadratic branch weights have no third-order inclusion-exclusion term. -/
theorem sorkin_third_order_cancellation (v : α → R) (A B C : Finset α)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    amplitudeWeight v (A ∪ B ∪ C) - amplitudeWeight v (A ∪ B) -
        amplitudeWeight v (A ∪ C) - amplitudeWeight v (B ∪ C) +
        amplitudeWeight v A + amplitudeWeight v B + amplitudeWeight v C = 0 := by
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  simp only [amplitudeWeight, Finset.sum_union hABC, Finset.sum_union hAB,
    Finset.sum_union hAC, Finset.sum_union hBC, star_add]
  ring

end D5.S3.Quantum.SorkinThirdOrder
