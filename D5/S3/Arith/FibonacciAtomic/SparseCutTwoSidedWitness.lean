/- GID: D5/S3/Arith/FibonacciAtomic/SparseCutTwoSidedWitness
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SparseCutTwoSidedWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Missing and extra sparse window cuts have actual witnesses beyond every bound. -/

import D5.S1.Digit.Infinite.SparseWindowMutualDetermination

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SparseCutTwoSidedWitness

open D5.S1.Digit.Infinite.WindowCylinderPartition
open D5.S1.Digit.Infinite.SparseWindowMutualDetermination

/-- A missing target cut obstructs decoding, and an extra observation cut obstructs
prediction, with both obstructions witnessed by actual sources above any bound. -/
theorem result (m M : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) (S : Finset ℕ) (B0 : ℕ) :
    ((∃ k ∈ Finset.Icc 1 (G M), k ∉ cuts m S) →
      ∃ a b : ℕ, B0 < a ∧ B0 < b ∧
        sigma m S a = sigma m S b ∧ q M a ≠ q M b) ∧
    ((∃ k ∈ cuts m S, k ∉ Finset.Icc 1 (G M)) →
      ∃ a b : ℕ, B0 < a ∧ B0 < b ∧
        q M a = q M b ∧ sigma m S a ≠ sigma m S b) := by
  constructor
  · rintro ⟨k, hk, hnot⟩
    exact missing_cut_witness m M hm hmM S k hk hnot B0
  · rintro ⟨k, hk, hnot⟩
    exact extra_cut_witness m M hm hmM S k hk hnot B0

end D5.S3.Arith.FibonacciAtomic.SparseCutTwoSidedWitness
