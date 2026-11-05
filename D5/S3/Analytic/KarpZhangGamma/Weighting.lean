/- GID: D5/S3/Analytic/KarpZhangGamma/Weighting
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Weighting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset, mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: One negative-to-positive sign change permits increasing coefficientwise weights. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
admission_basis: escape-witness
content theorem: weighted_sum_nonneg.
escape_witness: A least positive index separates the nonpositive prefix from the
nonnegative suffix. If there is no positive index, the nonnegative total
forces all summands to vanish. Subtracting the separating weight proves
the inequality, including zeros and empty sign groups. The coefficientwise
specialization inherits this same-delivery content.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* weighted_sum_nonneg: proof_shape: content; escape_witness: weighted_sum_nonneg;
  consumers: coefficientwise_weighting.
* coefficientwise_weighting: proof_shape: content; escape_witness: weighted_sum_nonneg;
  consumers: KarpZhangGamma.Smoothing.smoothed_weighting.

Direct frozen D5 dependencies, with same-delivery helpers recursively inlined:
none.
All KarpZhang dependencies are same-delivery declarations.
Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Analytic.KarpZhangGamma.Weighting

/-- The finite one-sign-change weighting principle. Zeros may occur anywhere.
The sign hypothesis excludes a positive term followed by a negative term. -/
theorem weighted_sum_nonneg (A W : ℕ → ℝ) (h : ℕ)
    (hsign : ∀ i ≤ h, ∀ j ≤ h, i < j → 0 < A i → 0 ≤ A j)
    (htotal : 0 ≤ ∑ i ∈ range (h + 1), A i)
    (hW : ∀ i ≤ h, 0 ≤ W i)
    (hmono : ∀ i ≤ h, ∀ j ≤ h, i ≤ j → W i ≤ W j) :
    0 ≤ ∑ i ∈ range (h + 1), A i * W i := by
  classical
  by_cases hp : ∃ q, q ≤ h ∧ 0 < A q
  · let q := Nat.find hp
    have hq : q ≤ h ∧ 0 < A q := Nat.find_spec hp
    have hterm : ∀ i ∈ range (h + 1), 0 ≤ A i * (W i - W q) := by
      intro i hi
      have hi' : i ≤ h := Finset.mem_range_succ_iff.mp hi
      by_cases hiq : i < q
      · have hai : A i ≤ 0 := by
          by_contra hnot
          exact Nat.find_min hp hiq ⟨hi', lt_of_not_ge hnot⟩
        exact mul_nonneg_of_nonpos_of_nonpos hai
          (sub_nonpos.mpr (hmono i hi' q hq.1 (le_of_lt hiq)))
      · have hai : 0 ≤ A i := by
          by_cases heq : i = q
          · simpa only [heq] using le_of_lt hq.2
          · exact hsign q hq.1 i hi' (lt_of_le_of_ne (Nat.le_of_not_gt hiq)
              (Ne.symm heq)) hq.2
        exact mul_nonneg hai
          (sub_nonneg.mpr (hmono q hq.1 i hi' (Nat.le_of_not_gt hiq)))
    have hid : (∑ i ∈ range (h + 1), A i * W i) =
        (∑ i ∈ range (h + 1), A i * (W i - W q)) +
          (∑ i ∈ range (h + 1), A i) * W q := by
      rw [sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hid]
    exact add_nonneg (sum_nonneg hterm) (mul_nonneg htotal (hW q hq.1))
  · have hnonpos : ∀ i ∈ range (h + 1), A i ≤ 0 := by
      intro i hi
      by_contra hnot
      exact hp ⟨i, Nat.le_of_lt_succ (mem_range.mp hi), lt_of_not_ge hnot⟩
    have hz : (∑ i ∈ range (h + 1), A i) = 0 :=
      le_antisymm (sum_nonpos hnonpos) htotal
    have hall := (sum_eq_zero_iff_of_nonpos hnonpos).mp hz
    have hwzero : (∑ i ∈ range (h + 1), A i * W i) = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [hall i hi, zero_mul]
    rw [hwzero]

/-- Apply the finite principle independently in every coefficient degree.
No convergence, bounded support, or division by a series is involved. -/
theorem coefficientwise_weighting (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (h : ℕ)
    (hsign : ∀ i ≤ h, ∀ j ≤ h, i < j → 0 < A i → 0 ≤ A j)
    (htotal : 0 ≤ ∑ i ∈ range (h + 1), A i)
    (hW : ∀ N i, i ≤ h → 0 ≤ W i N)
    (hmono : ∀ N i, i ≤ h → ∀ j, j ≤ h → i ≤ j → W i N ≤ W j N) :
    ∀ N, 0 ≤ ∑ i ∈ range (h + 1), A i * W i N := by
  intro N
  exact weighted_sum_nonneg A (fun i => W i N) h hsign htotal (hW N) (hmono N)

end D5.S3.Analytic.KarpZhangGamma.Weighting
