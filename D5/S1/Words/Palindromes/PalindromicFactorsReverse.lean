/- GID: D5/S1/Words/Palindromes/PalindromicFactorsReverse
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For every word, reversal preserves its palindromic factors and their cardinality; an infix's palindromic factors are included in those of the containing word. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Palindrome
import D5.S1.Words.Palindromes.PalindromicFactors

/- Provenance: Native proof over pinned mathlib. -/

/-! SEARCH RECEIPT

Repository reuse:
* `D5/S1/Words/Palindromes/PalindromicFactors.lean:23-27` provides
  `mem_palindromicFactors`, the membership characterization used by both finset proofs.
* The same file at lines 38-42 has a private theorem named
  `palindromicFactors_mono_of_infix`. Because it is private, it cannot provide the public
  monotonicity interface established here.

Pinned-library reuse:
* `Mathlib/Data/Finset/Defs.lean:144-146` provides `Finset.ext`.
* Lean core `Init/Data/List/Sublist.lean:832-839` provides `List.reverse_infix` and its
  forward implication `List.IsInfix.reverse`. This is the requested reversal-of-infix result;
  it is defined in Lean core rather than under `Mathlib/Data/List`.
* Lean core `Init/Data/List/Lemmas.lean:2483` provides `List.reverse_reverse`.
* `Mathlib/Data/List/Palindrome.lean:51-53` provides `List.Palindrome.reverse_eq`.
* Lean core `Init/Data/List/Sublist.lean:729-730` provides `List.IsInfix.trans`.

Negative findings:
* `rg -n 'palindromicFactors_reverse|reverse_palindromicFactors|palindromicFactors_subset_of_infix'
  D5 --glob '!D5/S1/Words/Palindromes/PalindromicFactorsReverse.lean'` returned zero hits; there is
  no pre-existing public reversal or monotonicity declaration under any of those names.
* `rg -n -i 'isInfix.*reverse|reverse.*isInfix|infix.*reverse|reverse.*infix'
  .lake/packages/mathlib/Mathlib` returned zero hits. Extending the search to the pinned Lean
  core located the result cited above, so no inline reconstruction is needed.
-/

namespace D5.S1.Words.Palindromes.PalindromicFactorsReverse

/-- Reversing a finite word leaves its finset of palindromic factors unchanged. -/
theorem palindromicFactors_reverse {alpha : Type*} [DecidableEq alpha] (w : List alpha) :
    palindromicFactors w.reverse = palindromicFactors w := by
  apply Finset.ext
  intro u
  rw [mem_palindromicFactors, mem_palindromicFactors]
  constructor
  · rintro ⟨hu, hpal⟩
    exact ⟨by simpa only [hpal.reverse_eq, List.reverse_reverse] using hu.reverse, hpal⟩
  · rintro ⟨hu, hpal⟩
    exact ⟨by simpa only [hpal.reverse_eq] using hu.reverse, hpal⟩

/-- This is the one-step cardinality consequence of `palindromicFactors_reverse`. -/
theorem palindromicFactors_reverse_card {alpha : Type*} [DecidableEq alpha] (w : List alpha) :
    (palindromicFactors w.reverse).card = (palindromicFactors w).card := by
  rw [palindromicFactors_reverse]

/-- Palindromic factors are monotone under contiguous-factor inclusion. -/
theorem palindromicFactors_subset_of_infix {alpha : Type*} [DecidableEq alpha]
    {u w : List alpha} (h : u <:+: w) : palindromicFactors u ⊆ palindromicFactors w := by
  intro p hp
  rw [mem_palindromicFactors] at hp ⊢
  exact ⟨hp.1.trans h, hp.2⟩

#print axioms palindromicFactors_reverse
#print axioms palindromicFactors_reverse_card
#print axioms palindromicFactors_subset_of_infix

end D5.S1.Words.Palindromes.PalindromicFactorsReverse
