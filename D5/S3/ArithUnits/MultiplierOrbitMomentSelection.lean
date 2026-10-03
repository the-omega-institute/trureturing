/- GID: D5/S3/ArithUnits/MultiplierOrbitMomentSelection
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MultiplierOrbitMomentSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nontrivial multiplier eigenvalues annihilate invariant-set power sums. -/

import Mathlib

/- Library-search audit trail (2026-09-28):
   * `MulChar.sum_eq_zero_of_ne_one` sums a nontrivial character over an entire finite ring;
     it does not apply to an arbitrary invariant subset.
   * `CyclicPlaneTwelveMultiplierObstruction.orderOf_dvd_card_erase_zero_of_image_mul_eq`
     constrains the cardinality of an invariant subset, not its power moments.
   * `Finset.sum_image` and `eq_zero_of_mul_eq_self_left` supply the reindexing and
     cancellation steps; the multiplier-eigenvalue equation is established below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.MultiplierOrbitMomentSelection

open Classical in
/-- The `k`-th power sum of a finite set vanishes when multiplication by `u` permutes
the set and acts nontrivially on that moment. -/
theorem power_sum_zero_of_mul_invariant
    {K : Type*} [Field K] (S : Finset K) (u : K) (k : ℕ)
    (hu : u ≠ 0)
    (hinv : S.image (fun x => u * x) = S)
    (hpow : u ^ k ≠ 1) :
    ∑ x ∈ S, x ^ k = 0 := by
  classical
  have hinj : Function.Injective (fun x : K => u * x) :=
    fun _ _ h => mul_left_cancel₀ hu h
  have hsum : (∑ x ∈ S, x ^ k) = u ^ k * ∑ x ∈ S, x ^ k := by
    calc
      (∑ x ∈ S, x ^ k) = ∑ x ∈ S.image (fun x => u * x), x ^ k := by rw [hinv]
      _ = ∑ x ∈ S, (u * x) ^ k := by rw [Finset.sum_image hinj.injOn]
      _ = u ^ k * ∑ x ∈ S, x ^ k := by simp [mul_pow, Finset.mul_sum]
  exact eq_zero_of_mul_eq_self_left hpow hsum.symm

example :
    (({1, 2, 4} : Finset (ZMod 7)).image (fun x => 2 * x) = {1, 2, 4}) ∧
      (2 : ZMod 7) ^ 3 = 1 ∧
      (∑ x ∈ ({1, 2, 4} : Finset (ZMod 7)), x ^ 3) = 3 := by
  decide

#print axioms power_sum_zero_of_mul_invariant

end D5.S3.ArithUnits.MultiplierOrbitMomentSelection
