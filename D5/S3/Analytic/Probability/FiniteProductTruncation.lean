/- GID: D5/S3/Analytic/Probability/FiniteProductTruncation
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/FiniteProductTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact degree cutoffs for weighted products of nonnegative excess factors. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic

/-! A product of factors one plus a nonnegative excess admits a lower bound by
discarding terms above a chosen degree. Strictly positive weights make the
exactness criterion pointwise. -/

open scoped BigOperators

namespace D5.S3.Analytic.Probability.FiniteProductTruncation

open Classical in
private theorem tail_eq_zero_iff {I : Type*} [Fintype I] (d : ℕ)
    (g : I → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (∑ s ∈ (Finset.univ : Finset I).powerset.filter (fun s => d < s.card),
        ∏ i ∈ s, g i) = 0 ↔
      (Finset.univ.filter fun i => 0 < g i).card ≤ d := by
  let positive := (Finset.univ : Finset I).filter fun i => 0 < g i
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun s _ => Finset.prod_nonneg (fun i _ => hg i))]
  constructor
  · intro hz
    by_contra! hd
    have hmember : positive ∈
        (Finset.univ : Finset I).powerset.filter (fun s => d < s.card) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hd⟩
    have hpositive : 0 < ∏ i ∈ positive, g i :=
      Finset.prod_pos fun i hi => (Finset.mem_filter.mp hi).2
    exact hpositive.ne' (hz positive hmember)
  · intro hcard s hs
    by_contra hn
    have hsubset : s ⊆ positive := by
      intro i hi
      have hne : g i ≠ 0 := fun hz => hn (Finset.prod_eq_zero hi hz)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne (hg i) hne.symm⟩
    exact (not_lt_of_ge ((Finset.card_le_card hsubset).trans hcard))
      (Finset.mem_filter.mp hs).2

open Classical in
/-- The expected terms through degree `d` lower bound the full weighted
product. The bound is exact when each assignment has at most `d` positive
excesses. -/
theorem weighted_product_truncation {Y I : Type*} [Fintype Y] [Fintype I]
    (d : ℕ) (w : Y → ℝ) (g : Y → I → ℝ)
    (hw : ∀ y, 0 < w y) (hg : ∀ y i, 0 ≤ g y i) :
    let subsets := (Finset.univ : Finset I).powerset
    let truncated := ∑ y, w y *
      ∑ s ∈ subsets.filter (fun s => s.card ≤ d), ∏ i ∈ s, g y i
    let full := ∑ y, w y * ∏ i, (1 + g y i)
    truncated ≤ full ∧
      (full = truncated ↔ ∀ y, (Finset.univ.filter fun i => 0 < g y i).card ≤ d) := by
  intro subsets truncated full
  let tail (y : Y) :=
    ∑ s ∈ subsets.filter (fun s => d < s.card), ∏ i ∈ s, g y i
  have hsplit (y : Y) :
      (∏ i, (1 + g y i)) =
        (∑ s ∈ subsets.filter (fun s => s.card ≤ d), ∏ i ∈ s, g y i) + tail y := by
    rw [Finset.prod_one_add]
    change ∑ s ∈ subsets, ∏ i ∈ s, g y i = _
    simpa only [tail, not_le] using
      (Finset.sum_filter_add_sum_filter_not subsets (fun s => s.card ≤ d)
        (fun s => ∏ i ∈ s, g y i)).symm
  have hfull : full = truncated + ∑ y, w y * tail y := by
    simp only [full, truncated, hsplit, mul_add, Finset.sum_add_distrib]
  have hnonneg (y : Y) : 0 ≤ w y * tail y :=
    mul_nonneg (hw y).le
      (Finset.sum_nonneg fun s _ => Finset.prod_nonneg fun i _ => hg y i)
  refine ⟨hfull ▸ le_add_of_nonneg_right (Finset.sum_nonneg fun y _ => hnonneg y), ?_⟩
  rw [hfull, add_eq_left, Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnonneg y]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero, (hw _).ne', false_or]
  exact forall_congr' fun y => tail_eq_zero_iff d (g y) (hg y)

end D5.S3.Analytic.Probability.FiniteProductTruncation
