---
bibkey: sahasrabudhe2015constantadditive
authors: Julian Sahasrabudhe
year: 2015
title: Sturmian Words and Constant Additive Complexity
doi: 10.5281/zenodo.10456215
url: https://math.colgate.edu/~integers/p30/p30.pdf
claim: Section 5 asks whether enumerating finite source words and then applying a finite morphism can produce fixed even additive complexity.
strata_touched:
  - D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.5281/zenodo.10456215

Source: https://math.colgate.edu/~integers/p30/p30.pdf

INTEGERS 15 (2015), Paper A30. The DOI identifies the archival copy of the journal article. No arXiv identifier is supplied for this source.

## Construction question

Section 5, printed p. 7:

> “Indeed, enumerate all words of finite length on the alphabet {0, . . . , n}, and form an infinite word w by concatenating all of the finite words in the order specified by the enumeration.”
>
> “Then apply the morphism defined by”
>
> 0 ↦ (0)(2n)   1 ↦ (1)(2n − 1)   ···   n ↦ (n)(n).
>
> “It is easy to check that the resulting word has additive complexity exactly 2n + 1. This construction suggests that recurrent words with fixed additive complexity are much more abundant than the class of generalized sturmian words. Can a construction of this form be generalized to give constructions of words with fixed even complexity?”

The corresponding proposition quantifies over every finite nonempty alphabet, every word containing all finite source words, and every finite integer-valued morphism with infinite output. Empty codewords are permitted. It rules out positive constant even additive complexity for this construction.

## Additive complexity

Section 2, printed p. 1:

> “A block b of a word w is a sequence of consecutive elements of w, that is b = wₖ ··· wₖ′ for k ≤ k′.”

> “For a block b = wₖ ··· wₖ′ of w, we define Σb := ∑ᵢ₌ₖᵏ′ wᵢ.”

 Section 2, printed p. 2:

> “The additive complexity of an infinite word w over a finite set of integers is the function ρ⁺(w, n) that counts the number of distinct sums obtained by summing n consecutive symbols of w.”

The source writes ρ⁺(w; n) = |{∑ᵢ₌ₗˡ⁺ⁿ⁻¹ wᵢ : l ∈ ℕ}|. The Lean statement starts at index zero and counts distinct integer sums with Set.ncard; positive values ensure finiteness whenever that count is used in the argument.

## Scope

The repository-derived obstruction uses equal sums of equal-length complete images, semigroup padding of codeword lengths, and reflection of a factor-sum set with one fixed point. Sahasrabudhe's Theorem 2 constructs every constant K > 1 through a different generalized-Sturmian input language; the obstruction does not negate that theorem. Classification of all morphisms giving constant odd complexity and extensions to other source factor languages remain open here.

## Experiments

The finite exact-arithmetic checker is in the-omega-institute/trureturing-experiments at commit e54bc2be9b628087de72d10e740d6afc3089e25f, docs/reports/sahasrabudhe-even-additive-complexity-morphism/check.py, SHA-256 ffad607841a6992894f66266b4d37a76f694157713bf6b2a2716cb5c20994a35. Running `python3 docs/reports/sahasrabudhe-even-additive-complexity-morphism/check.py` in that repository exits 0 with `ALL_CHECKS_OK`. Its finite samples and two-codeword reflection checks are regression evidence, not a quantified proof.

## Literature boundary

Issue #22635 records the source and adjacent-literature screen, including Banero, Dekking, and Popoli–Shallit–Stipulanti. Literature completeness is ASSUMED-UNVERIFIED. The source question is interpreted as the universal-input finite-morphism construction specified above.
