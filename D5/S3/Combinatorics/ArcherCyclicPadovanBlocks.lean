/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanBlocks
   mirror-E: none(waiver:ordered-block-decomposition-for-cyclic-padovan-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Separated blocks partitioning an interval occupy consecutive value ranges. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanBlocks

theorem low_block_perm_initial (a : ℕ) (low high : List ℕ)
    (hperm : (low ++ high).Perm (List.range' a (low.length + high.length)))
    (hsep : ∀ x ∈ low, ∀ y ∈ high, x < y) :
    low.Perm (List.range' a low.length) := by
  let sLow := low.mergeSort (· ≤ ·)
  let sHigh := high.mergeSort (· ≤ ·)
  have hlow : sLow.Perm low := List.mergeSort_perm low (· ≤ ·)
  have hhigh : sHigh.Perm high := List.mergeSort_perm high (· ≤ ·)
  have hsort : (sLow ++ sHigh).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨List.pairwise_mergeSort' (· ≤ ·) low,
      List.pairwise_mergeSort' (· ≤ ·) high, ?_⟩
    intro x hx y hy
    exact (hsep x (hlow.mem_iff.mp hx) y (hhigh.mem_iff.mp hy)).le
  have hrange : (List.range' a (low.length + high.length)).Pairwise (· ≤ ·) :=
    List.pairwise_le_range' _
  have hcanon : sLow ++ sHigh = List.range' a (low.length + high.length) :=
    ((hlow.append hhigh).trans hperm).eq_of_pairwise' hsort hrange
  have htake := congrArg (List.take low.length) hcanon
  have hlen : sLow.length = low.length := hlow.length_eq
  have hsorted : sLow = List.range' a low.length := by
    simpa [hlen, List.take_append_of_le_length] using htake
  exact hlow.symm.trans (hsorted ▸ List.Perm.refl _)

end D5.S3.Combinatorics.ArcherCyclicPadovanBlocks
