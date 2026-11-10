/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centred products in a commutative ring expand as alternating subset sums. -/

import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Inclusion–exclusion for finite products of centred factors. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

set_option autoImplicit false

/-- Expanding a product of centred factors gives the alternating subset transform. -/
lemma prod_sub_one_expansion {ι R : Type*} [DecidableEq ι] [CommRing R]
    (D : Finset ι) (F : ι → R) :
    (∏ d ∈ D, (F d - 1)) =
      ∑ J ∈ D.powerset, (-1 : R) ^ (D.card - J.card) * ∏ d ∈ J, F d := by
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ)]
  exact mul_comm _ _

end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
