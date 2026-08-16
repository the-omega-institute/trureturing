/- GID: D5/S3/AnalyticClosure/PositiveSeriesTail
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/PositiveSeriesTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive tail term makes the total exceed its finite partial sum. -/

import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

namespace D5.S3.AnalyticClosure.PositiveSeriesTail

/-- A summable nonnegative real series strictly exceeds any finite partial sum
that omits at least one strictly positive term. -/
theorem finite_partial_sum_lt_tsum_of_pos_outside
    (term : ℕ → ℝ) (window : Finset ℕ)
    (h_nonneg : ∀ n, 0 ≤ term n) (h_summable : Summable term)
    (h_tail : ∃ n ∉ window, 0 < term n) :
    ∑ n ∈ window, term n < ∑' n, term n := by
  let clipped := fun n => if n ∈ window then term n else 0
  obtain ⟨i, hi, hpos⟩ := h_tail
  have hlt : (∑' n, clipped n) < ∑' n, term n := by
    apply Summable.tsum_lt_tsum_of_nonneg (i := i)
    · intro n
      simp only [clipped]
      split_ifs
      · exact h_nonneg n
      · exact le_rfl
    · intro n
      simp only [clipped]
      split_ifs
      · exact le_rfl
      · exact h_nonneg n
    · simpa [clipped, hi] using hpos
    · exact h_summable
  calc
    ∑ n ∈ window, term n = ∑' n, clipped n := by
      symm
      rw [tsum_eq_sum (s := window) (by intro n hn; simp [clipped, hn])]
      simp [clipped]
    _ < ∑' n, term n := hlt

#print axioms finite_partial_sum_lt_tsum_of_pos_outside

end D5.S3.AnalyticClosure.PositiveSeriesTail
