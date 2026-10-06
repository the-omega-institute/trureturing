---
bibkey: frid2018numerationpalindromes
authors: Anna E. Frid
year: 2018
title: Representations of palindromes in the Fibonacci word
doi: null
url: https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf
claim: Conjecture 2 asks for the minimal palindromic decomposition length of the Fibonacci prefix with Zeckendorf length (100)^(2k-1)101; the same abstract states the matching upper bound.
strata_touched:
  - D5/S1/Words/Palindromes/FridPrefix/PalindromicLength
  - D5/S1/Words/Palindromes/FridPrefix/FridNumerals
  - D5/S1/Words/Palindromes/FridPrefix/CanonicalNecessity
  - D5/S1/Words/Palindromes/FridPrefix/FridUpper
  - D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength
license: citation-only
triage: anchor
---

# Representations of palindromes in the Fibonacci word

## Verified locator

Numeration 2018 book of abstracts, printed pages 9–12:
https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf

## Source statements

The definition on printed page 9:

> The palindromic length of a finite word u is the minimal number Q of palindromes P₁, . . . , P_Q such that u = P₁ · · · P_Q.

Conjecture 2, printed page 12:

> For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.

The following sentence, on the same page:

> We proved that 2k + 1 palindromes are enough for this word, so, it remains just to prove that this is the minimal possible value.

Digits are read most significant first with Fibonacci weights 1, 2, 3, 5, …
from the least significant position. The notation `(100)²ᵏ⁻¹101` concatenates
`2k−1` copies of `100` and one copy of `101`; it is a numeral, not a word
factor. Prefixes and word positions use zero-based indexing. Palindromic
length counts nonempty palindrome factors.

Theorem 1, printed pages 10–11:

> Let w be a characteristic Sturmian word corresponding to the directive sequence (dₙ), and w(i..j] = w[i + 1] . . . w[j] be a palindrome. Denote the Ostrowski representation of i as i = xₙ ··· xₘ ··· x₀ [o]; note that it may start with several leading zeros. Then there exist a legal representation of j given by j = xₙ ··· xₘ₊₁ yₘ · (dₘ₋₁ − xₘ₋₁) ··· (d₀ − x₀), where 0 ≤ m ≤ n and xₘ < yₘ ≤ dₘ.

The abstract states this characterization without a proof. For the Fibonacci
directive sequence every dₘ equals one. Its zero-digit necessity follows from
the formal reconstruction of a legal complementary numeral and zero terminal
Fibonacci residuals.
