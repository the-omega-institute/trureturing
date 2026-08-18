/- GID: D5/S3/Analytic/PartialSummation/AbelSummation
   generality: G
   mirror-B: D5/B/S3/Analytic/PartialSummation/AbelSummation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Abel summation by parts for a weighted range sum. -/

import Mathlib.Algebra.BigOperators.Module

namespace D5.S3.Analytic.PartialSummation.AbelSummation

/-- Finite Abel summation (summation by parts) for a range sum.

This is the finite algebraic step used in the source's localization chain; the
analytic remainder and zero-free-arc claims are outside this clause's scope.
-/
theorem abel_summation_range {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (g : ℕ → M) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i • g i) =
      f (n - 1) • (∑ i ∈ Finset.range n, g i) -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • (∑ j ∈ Finset.range (i + 1), g j) := by
  exact Finset.sum_range_by_parts f g n

#print axioms abel_summation_range

end D5.S3.Analytic.PartialSummation.AbelSummation
