---
bibkey: glensimpsonsmyth2017lyndonfactors
authors: Amy Glen, Jamie Simpson, and W. F. Smyth
year: 2017
title: Counting Lyndon factors
doi: 10.37236/6915
url: https://arxiv.org/abs/1701.00928v1
claim: "Open Problem 1 asks whether at every length the least number of distinct Lyndon factors among Lyndon words is attained by a Christoffel word."
strata_touched:
  - D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.37236/6915

Source: https://arxiv.org/abs/1701.00928v1

Electronic Journal of Combinatorics 24(3), P3.28. Page numbers below refer
to arXiv:1701.00928v1.

## Source statements

Section 6, p. 9, Open Problem 1:

“Is it true that the minimum number of distinct Lyndon factors over all
Lyndon words of the same length is attained by at least one Christoffel
word of that length?”

Section 1, p. 1:

“A finite word z is said to be a factor of a given finite word w if there
exist words u, v such that w = uzv.”

Section 1, p. 2:

“A Lyndon word over Σ is a non-empty primitive word that is the
lexicographically least word in its conjugacy class, i.e., w ∈ Σ or w < vu
for all non-empty words u, v such that w = uv (e.g., see [10]).”

Section 5, p. 8:

“Let L(w) denote the number of distinct Lyndon factors in a word w.”

“The so-called Christoffel word of slope p/q beginning with the letter a
is the unique Sturmian Lyndon word over {a, b} of length q containing p
occurrences of the letter b, given by:” followed by aPal(v)b.

The finite-word encoding uses positions starting at zero and letters in
Fin k. The lower Christoffel word has letter 1 precisely when
⌊(i + 1)p/n⌋ − ⌊ip/n⌋ = 1. The comparison ranges over n ≥ 2,
0 < p < n with p coprime to n, and every Lyndon competitor over every
finite ordered alphabet. Equal factor lists are counted once; letters
and the whole Lyndon word are included.

## Counterexample and boundary

For U = aabaabab, V = aabab and v = ababbababbabbababbabb, replace a by
UUV and b by UUVV. The resulting binary word has length 506 and sixteen
distinct Lyndon factors. Seventeen distinct Lyndon-factor witnesses for
each of the 220 eligible Christoffel numerators give a strict separation.
The formal argument checks the actual factors, without assuming the
source's continued-fraction count or general morphism identities.

The global minimum at 506, the earliest counterexample length, and
alphabet reduction remain open here. Theorem 8 is a count within the
Christoffel family and does not depend on Open Problem 1; its statement
is unaffected. No other source theorem is refuted by this argument.

## Literature boundary

Amy Glen, “On the Stern–Brocot tree, continued fractions, and Lyndon
words”, 41ACCMCC talk, slide 19, announces an affirmative answer:
“Question: Is it true that, for each integer n ≥ 2, there exists a
Christoffel word of length n that contains the fewest number of Lyndon
factors for that length? Answer: Yes — it can be proved using some
interrelated properties of the Stern–Brocot tree, continued fractions,
and Christoffel words.” This conflicts with the counterexample above.
The supplied slides contain no proof of that announcement.

The literature screen recorded in issue
https://github.com/the-omega-institute/trureturing/issues/18581 found
no published proof or counterexample in the sources it inspected.
Completeness, priority and the missing argument behind the announcement
are ASSUMED-UNVERIFIED.

Supplementary experiment: the-omega-institute/trureturing-experiments,
`docs/reports/glen-simpson-smyth-2017-open-problem-1-christoffel-minimum/verify506.py`,
commit `4c708c7738167c01f27b16ea993eaf92e66d766a`, SHA-256
`9c9b9e90fd40e1a29042df31d674f5d637e4f444f738ed51c5342de4930600d4`.
Issue #18581 records exit 0 and `RESULT PASS`. The experiment is
supplementary evidence; the formal refutation uses kernel certificates.
