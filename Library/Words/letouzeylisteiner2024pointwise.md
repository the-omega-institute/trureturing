---
bibkey: letouzeylisteiner2024pointwise
authors: Pierre Letouzey, Shuo Li, Wolfgang Steiner
year: 2024
title: Pointwise order of generalized Hofstadter functions G, H and beyond
doi: null
url: https://arxiv.org/abs/2410.00529v2
claim: The original k=3 Hofstadter recurrence has a unique total realization, and H(n) is n minus the number of letters 1 in the original morphic prefix of length n.
strata_touched:
  - D5/S1/Words/Hofstadter/OriginalHFoundation
license: citation-only
triage: anchor
---

# Original Hofstadter H and morphic prefix counts

## Verified locator

The canonical paper version is https://arxiv.org/abs/2410.00529v2.
The bibkey year refers to the initial arXiv submission. The numerical
definition in Section 1 specializes at k=3 to H(0)=0 and
H(n+1)=n+1-H(H(H(n))), on natural numbers. The original substitution
specializes to 1 -> 2, 2 -> 3, 3 -> 31, with fixed word rooted at 3.

Theorem 3.1 relates iterates of the generalized Hofstadter function to
lengths of substituted prefixes. Proposition 4.1, equation (4.2), at k=3
and j=1 gives H(n) as the number of letters greater than 1 among the first
n letters, for every n>=0. Complementing this count gives
H(n)+count1(prefix_n)=n, including n=0 and every whole-block endpoint.
Propositions 4.2 and 4.3 give related substitution-length and increment
identities; they are context, not additional conclusions of this unit.

The author's Coq development is pinned at
https://github.com/letouzey/hofstadter_g/tree/dde0281c7a92550806f264112692da9165543942.
In GenG.v, recf, f, f_recf, f_eqn and f_unique supply the bounded-depth
construction and numerical uniqueness argument. In Words.v, ksubst,
kword, kseq, f_count_0, count_kseq, kword_len and kprefix_firstn_kword
give the external morphic correspondence. Its letters 0,1,2 correspond
respectively to the paper's original letters 1,2,3; its root 2 becomes 3,
and its counted letter 0 becomes 1.

That repository's LICENSE places Pierre Letouzey's Coq development in
the public domain, except the unrelated HalfQuantum subdirectory and
documents in poster, reports and talks. The numerical construction here
adapts the GenG.v argument. The finite arbitrary-cut counting argument
and semantic bridges are Lean proofs; the external Coq source is
mathematical guidance, not an imported Lean proof or a new axiom.
No mathematical novelty or exhaustive supplier-absence claim is made.

The result concerns exact values and original word prefixes. It supplies
no machine, input-acquisition procedure, serialization, resource bound,
frequency theorem or quantitative automaton lower bound.
