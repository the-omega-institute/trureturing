/- GID: D5/S3/Factorization/HilbertMonoidNonUnique
   generality: G
   mirror-B: D5/B/S3/Factorization/HilbertMonoidNonUnique
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Hilbert monoid of positive naturals congruent to 1 mod 4 does not have unique factorization: 441 = 9·49 = 21·21 are two factorizations into H-irreducibles (9, 21, 49) whose multisets of factors differ. -/

import Mathlib

namespace D5.S3.Factorization.HilbertMonoidNonUnique

/-- The Hilbert monoid: positive naturals congruent to `1 mod 4`, closed under multiplication. -/
def inH (n : ℕ) : Prop := n % 4 = 1

instance (n : ℕ) : Decidable (inH n) := by unfold inH; infer_instance

/-- An element is `H`-irreducible if it lies in `H`, exceeds one, and every factorization
into two `H`-elements is trivial. -/
def HIrreducible (n : ℕ) : Prop :=
  inH n ∧ 1 < n ∧ ∀ a ∈ n.divisors, inH a → inH (n / a) → a = 1 ∨ a = n

instance (n : ℕ) : Decidable (HIrreducible n) := by unfold HIrreducible; infer_instance

theorem hIrreducible_nine : HIrreducible 9 := by decide
theorem hIrreducible_twentyOne : HIrreducible 21 := by decide
theorem hIrreducible_fortyNine : HIrreducible 49 := by decide

/-- Non-unique factorization in the Hilbert monoid: `441 = 9·49 = 21·21` are two
factorizations into `H`-irreducibles with distinct multisets of factors. -/
theorem hilbert_monoid_factorization_not_unique :
    HIrreducible 9 ∧ HIrreducible 49 ∧ HIrreducible 21 ∧
      (441 = 9 * 49 ∧ 441 = 21 * 21) ∧
      (({9, 49} : Multiset ℕ) ≠ {21, 21}) := by
  refine ⟨hIrreducible_nine, hIrreducible_fortyNine, hIrreducible_twentyOne,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  decide

end D5.S3.Factorization.HilbertMonoidNonUnique
