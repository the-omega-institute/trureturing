/- GID: D5/S3/Combinatorics/NumericalSemigroup/TwoWitnessResidues
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NumericalSemigroup/TwoWitnessResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two closest residue coefficients suffice to detect nonnegative vectors in a two-witness integer span. -/

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues

private theorem nonneg_between_primitive_coefficients
    {b t a c a' c' p u direction : ℤ} (hb : 0 < b) (ht : 0 ≤ t) (hp : 0 ≤ p)
    (sourceDegree : a * b + c = t) (targetDegree : a' * b + c' = t)
    (hc : 0 < c * direction) (hc' : 0 ≤ c' * direction)
    (difference : 0 ≤ (c - c') * direction) (source : 0 ≤ a * p + c * u) :
    0 ≤ a' * p + c' * u := by
  have slope : b * c * (a' * p + c' * u) =
      b * c' * (a * p + c * u) + (c - c') * (t * p) := by
    calc
      _ = c * ((a' * b + c') * p) + b * c * c' * u - c * c' * p := by ring
      _ = c * (t * p) + b * c * c' * u - c * c' * p := by rw [targetDegree]
      _ = c' * ((a * b + c) * p) + b * c' * c * u - c' * c * p +
          (c - c') * (t * p) := by rw [sourceDegree]; ring
      _ = _ := by ring
  have scaled : b * (c * direction) * (a' * p + c' * u) =
      b * (c' * direction) * (a * p + c * u) + ((c - c') * direction) * (t * p) := by
    calc
      _ = (b * c * (a' * p + c' * u)) * direction := by ring
      _ = _ := by rw [slope]; ring
  apply nonneg_of_mul_nonneg_right _ (Int.mul_pos hb hc)
  rw [scaled]
  exact add_nonneg (mul_nonneg (mul_nonneg hb.le hc') source)
    (mul_nonneg difference (mul_nonneg ht hp))

/-- For nonnegative degree, any feasible pair of integer coefficients implies
feasibility at one of the two closest representatives of the residual coefficient. -/
theorem nonnegative_at_nearest_residue {J : Type*} (p u : J → ℤ) (nonnegative : ∀ j, 0 ≤ p j)
    {b t : ℤ} (hb : 0 < b) (ht : 0 ≤ t) :
    let q := t / b
    let r := t % b
    (∃ a c : ℤ, a * b + c = t ∧ ∀ j, 0 ≤ a * p j + c * u j) ↔
      (∀ j, 0 ≤ q * p j + r * u j) ∨ (∀ j, 0 ≤ (q + 1) * p j + (r - b) * u j) := by
  let q := t / b
  let r := t % b
  have q_r : q * b + r = t := by
    simpa [q, r, mul_comm, add_comm] using Int.emod_add_mul_ediv t b
  have lo : 0 ≤ r := Int.emod_nonneg _ hb.ne'
  have hi : r < b := Int.emod_lt_of_pos _ hb
  have qr_back : (q + 1) * b + (r - b) = t := by linarith [q_r, show (q + 1) * b = q * b + b by ring]
  constructor
  · rintro ⟨a, c, eq, nn⟩
    have sameResidue : c % b = r := by
      dsimp only [r]
      rw [← eq, Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
    have division : r + b * (c / b) = c := by
      rw [← sameResidue, Int.emod_add_mul_ediv]
    rcases lt_trichotomy c 0 with negative | zero | positive
    · right
      have divLe : c / b ≤ -1 := by linarith [Int.ediv_neg_of_neg_of_pos negative hb]
      have mulLe := mul_le_mul_of_nonneg_left divLe hb.le
      have upper : c ≤ r - b := by linarith [division, mulLe]
      intro j
      exact nonneg_between_primitive_coefficients (direction := -1) hb ht (nonnegative j)
        eq qr_back (by simpa using neg_pos.mpr negative)
        (by simpa using sub_nonneg.mpr hi.le)
        (by simpa using sub_nonneg.mpr upper) (nn j)

    · left
      have r_zero : r = 0 := by simpa [zero] using sameResidue.symm
      have q_nn : 0 ≤ q := Int.ediv_nonneg ht hb.le
      intro j
      change 0 ≤ q * p j + r * u j
      simp only [r_zero, zero_mul, add_zero]
      exact mul_nonneg q_nn (nonnegative j)
    · left
      have mulNN := mul_nonneg hb.le (Int.ediv_nonneg positive.le hb.le)
      have bounded : r ≤ c := by linarith [division, mulNN]
      exact fun j => nonneg_between_primitive_coefficients (direction := 1) hb ht (nonnegative j)
        eq q_r (by simpa using positive) (by simpa using lo)
        (by simpa using sub_nonneg.mpr bounded) (nn j)
  · rintro (h | h)
    · exact ⟨q, r, q_r, h⟩
    · exact ⟨q+1, r-b, qr_back, h⟩

end D5.S3.Combinatorics.NumericalSemigroup.TwoWitnessResidues
