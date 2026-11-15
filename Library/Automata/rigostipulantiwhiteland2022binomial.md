---
bibkey: rigostipulantiwhiteland2022binomial
authors: Michel Rigo; Manon Stipulanti; Markus A. Whiteland
year: 2022
title: Characterizations of families of morphisms and words via binomial complexities
doi: 10.1016/j.ejc.2024.103932
url: https://arxiv.org/abs/2201.04603v2
claim: "Question C asks for words with unbounded abelian complexity and arbitrarily long strict binomial-complexity hierarchies terminating at factor complexity, and asks whether morphic witnesses exist."
strata_touched:
  - D5/S1/Words/Complexity/ThueMorseFactorRigidity
license: citation-only
triage: anchor
---

# Binomial-complexity hierarchies

## Verified locator

DOI: 10.1016/j.ejc.2024.103932

Source: https://arxiv.org/abs/2201.04603v2

The binding text is arXiv v2, Section 7.1, PDF page 30. The journal version is
European Journal of Combinatorics 118, article 103932.

## Question C

“For each ℓ ≥ 1, does there exist a word w (depending on ℓ) such that b_w^(1) is
unbounded and

\[
b_w^{(1)}\prec b_w^{(2)}\prec\cdots\prec b_w^{(\ell-1)}
\prec b_w^{(\ell)}=p_w?
\]

If the answer is positive, can we find a (pure) morphic such word w?”

Here the subscripts and superscripts transcribe the source's mathematical
notation. The finite alphabet is encoded by `Fin 4`; positions and factor lengths
are natural numbers. A factor is a function `Fin n → Fin 4`. Its binomial profile
records all scattered-pattern counts through order k, including the empty
pattern with count one. Binomial complexity counts the represented profiles;
factor complexity counts the distinct contiguous factors. The strict relation
means strict inequality at infinitely many natural arguments. The feasible range
retained by the hierarchy assertion is ℓ ≥ 2. The pure-morphic refinement is a
separate question.
