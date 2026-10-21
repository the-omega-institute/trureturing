/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Interface
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Interface
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed walk counts and the even coefficient comparison sequence. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Defs

noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.RegularCHS.Interface

/-- The total number of rooted closed walks of a given length. -/
noncomputable def closedWalks {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  ∑ v, ((G.adjMatrix ℕ) ^ k) v v

/-- The comparison sequence with constant coefficient one. -/
noncomputable def bseq (n r : ℕ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => (r : ℝ) * ((n : ℝ) + 2 * (m + 1) - 2) * bseq n r m /
      (2 * (m + 1))

@[simp] theorem bseq_zero (n r : ℕ) : bseq n r 0 = 1 := rfl

/-- The defining recurrence, with its positive denominator cleared. -/
theorem bseq_succ (n r m : ℕ) :
    (2 * (m + 1) : ℝ) * bseq n r (m + 1) =
      (r : ℝ) * ((n : ℝ) + 2 * (m + 1) - 2) * bseq n r m := by
  rw [bseq]
  have h : (2 * (m + 1) : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ _ h

/-- The recurrence indexed by a positive coefficient degree. -/
theorem bseq_recurrence (n r m : ℕ) (hm : 1 ≤ m) :
    (2 * m : ℝ) * bseq n r m =
      (r : ℝ) * ((n : ℝ) + 2 * m - 2) * bseq n r (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simpa [Nat.succ_eq_add_one] using bseq_succ n r k

end D5.S3.Combinatorics.Graph.RegularCHS.Interface
