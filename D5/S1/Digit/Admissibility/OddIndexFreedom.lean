/- GID: D5/S1/Digit/Admissibility/OddIndexFreedom
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/OddIndexFreedom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Odd indices make every subset nonadjacent, with exact powerset count. -/

/- Library-search audit trail (2026-08-16):
   * D5 has no equivalent odd-index admissibility and powerset-count theorem.
   * Pinned Mathlib has no combined theorem for this statement.
   * The proof reuses `Nat.Odd.add_one`, `Nat.not_even_iff_odd`,
     `Finset.card_erase_of_mem`, and `Finset.card_powerset`. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum

namespace D5.S1.Digit.Admissibility.OddIndexFreedom

/-- Every subset of odd natural indices satisfies the Zeckendorf
nonadjacency condition, and the nonempty subsets have the expected count. -/
theorem odd_index_subsets_are_admissible_and_counted
    (indices : Finset Nat) (hOdd : ∀ n ∈ indices, Odd n) :
    (∀ subset ∈ indices.powerset, ∀ n ∈ subset, n + 1 ∉ subset) ∧
      (indices.powerset.erase ∅).card = 2 ^ indices.card - 1 := by
  constructor
  · intro subset hsubset n hn hnSucc
    have hnIndices : n ∈ indices := Finset.mem_powerset.mp hsubset hn
    have hnSuccIndices : n + 1 ∈ indices :=
      Finset.mem_powerset.mp hsubset hnSucc
    have hnOdd : Odd n := hOdd n hnIndices
    have hnSuccOdd : Odd (n + 1) := hOdd (n + 1) hnSuccIndices
    exact (Nat.not_even_iff_odd.mpr hnSuccOdd) hnOdd.add_one
  · rw [Finset.card_erase_of_mem (by simp), Finset.card_powerset]

/- The source atom's twelve-index cone contains exactly 4095 nonempty subsets. -/
example (indices : Finset Nat) (hOdd : ∀ n ∈ indices, Odd n)
    (hCard : indices.card = 12) :
    (indices.powerset.erase ∅).card = 4095 := by
  rw [(odd_index_subsets_are_admissible_and_counted indices hOdd).2, hCard]
  norm_num

#print axioms odd_index_subsets_are_admissible_and_counted

end D5.S1.Digit.Admissibility.OddIndexFreedom
