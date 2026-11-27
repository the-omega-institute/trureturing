/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisExteriorPolarity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisExteriorPolarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A nonzero contribution in a zero-sum exterior row forces one of the opposite sign. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedNormalization

/-! A nonzero signed term at an exterior vertex forces a term of the opposite sign. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExteriorPolarity

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip)
open Q9FiveAxisSignedNormalization (rupFlipSign)

/-- In an exterior row with zero sum, a signed occupied neighbor has an
occupied neighbor making the opposite contribution. -/
theorem exists_opposite_contribution {n : ℕ} {s : Q n → ℤ} {x : Q n}
    (hunit : ∀ y, s y = 0 ∨ s y = 1 ∨ s y = -1)
    (hrow : ∑ i : Fin n, rupFlipSign i x * s (flip x i) = 0)
    (i : Fin n) (hi : s (flip x i) ≠ 0) :
    ∃ j : Fin n, rupFlipSign j x * s (flip x j) =
      -(rupFlipSign i x * s (flip x i)) := by
  classical
  let term (j : Fin n) := rupFlipSign j x * s (flip x j)
  have hsign (j : Fin n) : rupFlipSign j x = 1 ∨ rupFlipSign j x = -1 :=
    neg_one_pow_eq_or ℤ _
  have ht (j : Fin n) : term j = 0 ∨ term j = 1 ∨ term j = -1 := by
    rcases hsign j with hp | hp <;>
      rcases hunit (flip x j) with hz | hp' | hn' <;> norm_num [term, hp, *]
  have htn : term i ≠ 0 := by
    rcases hsign i with hp | hp <;> simp [term, hp, hi]
  change ∑ j : Fin n, term j = 0 at hrow
  change ∃ j : Fin n, term j = -term i
  by_contra! hnone
  rcases (ht i).resolve_left htn with hpos | hneg
  · have hnn (j : Fin n) (hj : j ∈ (Finset.univ : Finset (Fin n))) : 0 ≤ term j := by
      rcases ht j with hz | hp | hn
      · simp [hz]
      · simp [hp]
      · exact (hnone j (by simpa [hpos] using hn)).elim
    have hle := Finset.single_le_sum hnn (Finset.mem_univ i)
    rw [hrow, hpos] at hle
    omega
  · have hnn (j : Fin n) (hj : j ∈ (Finset.univ : Finset (Fin n))) : 0 ≤ -term j := by
      rcases ht j with hz | hp | hn
      · simp [hz]
      · exact (hnone j (by simpa [hneg] using hp)).elim
      · simp [hn]
    have hle := Finset.single_le_sum hnn (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib, hrow, hneg] at hle
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExteriorPolarity
