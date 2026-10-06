---
bibkey: fridlabordepeltomaki2021automaticppl
authors: Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki
year: 2021
title: "On prefix palindromic length of automatic words"
doi: 10.1016/j.tcs.2021.08.016
url: https://arxiv.org/abs/2009.02934v2
claim: "Section 5.1, Conjecture 17 asks whether the period-doubling PPL-difference is not 2-automatic and its prefix palindromic length is not 2-regular."
strata_touched:
  - D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength
  - D5/S1/Words/Palindromes/PeriodDoubling/Word
  - D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic
license: citation-only
triage: anchor
---

# Prefix palindromic length of automatic words

The journal version is Theoretical Computer Science 891, pages 13–23. Locators
below use the printed pages of arXiv:2009.02934v2.

Page 1: “In particular, we are interested in the minimal number of palindromes needed for such a decomposition, which we call the palindromic length of a word.” The example abbaba has length three, with factorizations (abba)(b)(a) and (a)(bb)(aba).

Page 1 defines the object: “here PPLᵤ(n) is defined as the palindromic length of
the prefix u[0] . . . u[n − 1] of length n of u.” Palindromic length is the
minimum number of palindrome factors. Empty factors may be removed, so the
minimum agrees with the convention of nonempty factors and an empty
factorization for the empty word.

Definition 3, page 2: “Let u be an infinite word. Then we define the
PPL-difference sequence dᵤ of u by setting dᵤ(n) = PPLᵤ(n + 1) − PPLᵤ(n) for
n ≥ 0.”

Section 5.1, page 12: “The period-doubling word u_pd is the 2-automatic word”
u_pd = φ_pd^ω(a) = abaaabababaaabaa…, where φ_pd(a) = ab and φ_pd(b) = aa. The Lean alphabet uses false for a and true for b. Infinite-word
indices start at zero; the valuation formula uses the positive index n + 1.

Conjecture 17, page 13, verbatim:

> The sequence $d_{pd}$ of the period-doubling word $\infw{u}_{pd}$ is {\rm not}
> $2$-automatic, and so the prefix palindromic length $\PPL_{pd}(n)$ of
> $\infw{u}_{pd}$ is not $2$-regular.

The source conjectures this statement. A finite prefix computation, or merely
infinitely many distinct kernel elements of PPL itself, does not establish it.

## Verified locator

DOI: https://doi.org/10.1016/j.tcs.2021.08.016

URL: https://arxiv.org/abs/2009.02934v2

Definition 3 is on printed page 2; Section 5.1 and Conjecture 17 are on printed pages 12–13 of arXiv:2009.02934v2.
