/- GID: D5/S3/Analytic/ExpRatioCM/Positive
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Positive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative exponential coefficients imply complete monotonicity. -/

import D5.S3.Analytic.ExpRatioCM.Series

/-! Positive exponential coefficients and complete monotonicity. -/

open scoped BigOperators Topology
open Set
open D5.S3.Analytic.ExpRatioCM.Defs
open D5.S3.Analytic.ExpRatioCM.Series

namespace D5.S3.Analytic.ExpRatioCM.Positive

/--
Termwise nonnegative exponential moments give the alternating-sign derivative
inequalities.  The derivative identity is supplied by the convergent-series
calculation in the application module; this lemma only records the positive
coefficient implication and is independent of the particular quotient.
-/
theorem cm_of_nonnegative_exponential_expansion
    {h : ℝ → ℝ} {c : ℕ → ℝ}
    (hsmooth : ContDiffOn ℝ ⊤ h (Ioi 0))
    (hderiv : ∀ k : ℕ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k h t = (-1 : ℝ) ^ k *
        (∑' n : ℕ, c n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t)))
    (hc : ∀ n : ℕ, 0 ≤ c n) :
    CompletelyMonotoneOn h := by
  refine ⟨hsmooth, ?_⟩
  intro k t ht
  rw [hderiv k t ht]
  rw [show (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k *
      (∑' n : ℕ, c n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t))) =
      ∑' n : ℕ, c n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t) by
    rw [← mul_assoc, ← pow_add, show k + k = 2 * k by omega]
    simp]
  exact tsum_nonneg (fun n =>
    mul_nonneg (mul_nonneg (hc n) (by positivity)) (le_of_lt (Real.exp_pos _)))

/--
The positive cases reduce to the preceding coefficient criterion.  The two
families of coefficient data are intentionally separated: the zeroth member
of the second family has the extra constant term, while all its positive
members agree with the first family.
-/
theorem cm_of_le_two
    (hF : ∀ i : ℕ, i ≤ 2 → ∃ c : ℕ → ℝ,
      (∀ n : ℕ, 0 ≤ c n) ∧
      (∀ k : ℕ, ∀ t : ℝ, 0 < t →
        iteratedDeriv k (ratioF i) t = (-1 : ℝ) ^ k *
          (∑' n : ℕ, c n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t))))
    (hG : ∀ i : ℕ, i ≤ 2 → ∃ c : ℕ → ℝ,
      (∀ n : ℕ, 0 ≤ c n) ∧
      (∀ k : ℕ, ∀ t : ℝ, 0 < t →
        iteratedDeriv k (ratioG i) t = (-1 : ℝ) ^ k *
          (∑' n : ℕ, c n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t)))) :
    ∀ i : ℕ, i ≤ 2 →
      CompletelyMonotoneOn (ratioF i) ∧ CompletelyMonotoneOn (ratioG i) := by
  intro i hi
  obtain ⟨cF, hcF, hdF⟩ := hF i hi
  obtain ⟨cG, hcG, hdG⟩ := hG i hi
  exact ⟨cm_of_nonnegative_exponential_expansion (contDiffOn_ratioF i) hdF hcF,
    cm_of_nonnegative_exponential_expansion (contDiffOn_ratioG i) hdG hcG⟩

end D5.S3.Analytic.ExpRatioCM.Positive
