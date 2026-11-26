---
bibkey: rigostipulantiwhiteland2022binomial
authors: Michel Rigo; Manon Stipulanti; Markus A. Whiteland
year: 2022
title: Characterizations of families of morphisms and words via binomial complexities
doi: 10.1016/j.ejc.2024.103932
url: https://arxiv.org/abs/2201.04603v2
claim: "Theorem 7.2 gives the strict binomial-complexity hierarchy of iterated Thue–Morse images of Sturmian words; Question C asks for words with unbounded abelian complexity and arbitrarily long strict binomial-complexity hierarchies terminating at factor complexity, and asks whether morphic witnesses exist."
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

## Theorem 7.2

ArXiv v2, Theorem 7.2 (paper.tex:3077–3080), states that for a Sturmian word
$s$ and the Thue–Morse morphism $\varphi$, the words
$s_k=\varphi^k(s)$ satisfy

\[
b_{s_k}^{(1)}\prec\cdots\prec b_{s_k}^{(k+1)}
\prec b_{s_k}^{(k+2)}=p_{s_k}.
\]

The definition `UniformWordRecurrence.Core.core k` is the Boolean-coded
Fibonacci instance of $\varphi^k(s)$, with the initial letter coding given by
Boolean complement. Its strict hierarchy components and terminal profile
injectivity implement this literature-attested hierarchy. The unbounded-abelian
Question C witnesses asserted by `ThueMorseFactorRigidity.result` and
`ThueMorseFactorRigidity.morphic_result` are separate results.
