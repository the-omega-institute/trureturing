/- GID: D5/S3/Arith/Coding/ReciprocityParityErrorDetection
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/ReciprocityParityErrorDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One sign flip changes a valid parity product, while two flips can restore it. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.Int.Units

/- Library-search audit trail (2026-08-25):
   * Repository name and body-shape searches found no finite sign-profile
     parity theorem or local-sign flip primitive.
   * Pinned Mathlib's `Int.units_eq_one_or` identifies `ℤˣ` with the intended
     sign carrier `{+1, -1}`.
   * Exact hit `Finset.prod_update_of_mem` computes the product after changing
     one reported coordinate. No library theorem packages all three clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.ReciprocityParityErrorDetection

open scoped BigOperators

universe u

/-- Flip one local sign while leaving every other reported symbol unchanged. -/
def flipLocalSign {ι : Type u} [DecidableEq ι]
    (profile : ι → ℤˣ) (place : ι) : ι → ℤˣ :=
  Function.update profile place (-profile place)

/--
For a valid finite sign report, any selected single flip changes the product to
`-1`. Two distinct single-error locations therefore have the same syndrome, so
the product check cannot locate the error. Flipping both selected locations
restores product `1`, giving an even-error pattern that the check accepts.
-/
theorem reciprocity_parity_error_detection {ι : Type u} [DecidableEq ι]
    (places : Finset ι) (profile : ι → ℤˣ) (first second : ι)
    (first_mem : first ∈ places) (second_mem : second ∈ places)
    (distinct : first ≠ second)
    (valid_product : ∏ place ∈ places, profile place = 1) :
    (∏ place ∈ places, flipLocalSign profile first place) = -1 ∧
      (∏ place ∈ places, flipLocalSign profile first place) =
        (∏ place ∈ places, flipLocalSign profile second place) ∧
      (∏ place ∈ places,
        Function.update (flipLocalSign profile first) second
          (-profile second) place) = 1 := by
  have flip_product (candidate : ι → ℤˣ) (place : ι)
      (place_mem : place ∈ places) :
      (∏ index ∈ places, flipLocalSign candidate place index) =
        -(∏ index ∈ places, candidate index) := by
    rw [flipLocalSign, Finset.prod_update_of_mem place_mem,
      Finset.sdiff_singleton_eq_erase]
    calc
      (-candidate place) * ∏ index ∈ places.erase place, candidate index =
          -(candidate place * ∏ index ∈ places.erase place, candidate index) :=
        neg_mul _ _
      _ = -(∏ index ∈ places, candidate index) := by
        rw [Finset.mul_prod_erase _ _ place_mem]
  have first_report :
      (∏ place ∈ places, flipLocalSign profile first place) = -1 := by
    rw [flip_product profile first first_mem, valid_product]
  have second_report :
      (∏ place ∈ places, flipLocalSign profile second place) = -1 := by
    rw [flip_product profile second second_mem, valid_product]
  have second_unchanged :
      flipLocalSign profile first second = profile second := by
    simp [flipLocalSign, Function.update_of_ne distinct.symm]
  have double_report :
      (∏ place ∈ places,
        Function.update (flipLocalSign profile first) second
          (-profile second) place) = 1 := by
    calc
      (∏ place ∈ places,
          Function.update (flipLocalSign profile first) second
            (-profile second) place) =
          -(∏ place ∈ places, flipLocalSign profile first place) := by
        rw [← second_unchanged]
        exact flip_product (flipLocalSign profile first) second second_mem
      _ = 1 := by rw [first_report]; simp
  exact ⟨first_report, first_report.trans second_report.symm, double_report⟩

#print axioms reciprocity_parity_error_detection

end D5.S3.Arith.Coding.ReciprocityParityErrorDetection
