---
bibkey: moree2013moser
authors: Pieter Moree
year: 2013
title: Moser's mathemagical work on the equation 1^k + 2^k + ... + (m−1)^k = m^k
doi: 10.1216/rmj-2013-43-5-1707
claim: "Theorem 2 (recording L. Moser, Scripta Math. 19 (1953) 84–88): if ∑_{i<m} i^k = m^k with m > 1, then for every prime p ∣ m−1: (p−1) ∣ k, p ∣ (m−1)/p + 1, p² ∤ m−1; hence m−1 is squarefree"
strata_touched:
  - D5/S3/PrimeForms/Obstructions/ErdosMoserLocalObstruction
license: citation-only
triage: anchor
---

# Moser's mathemagical work on the equation

Pieter Moree's survey records Moser's local congruence obstruction for a
solution of `1^k + 2^k + ... + (m - 1)^k = m^k`. Theorem 2, explicitly
attributed there to L. Moser's 1953 paper, states that every prime `p` dividing
`m - 1` satisfies `p - 1 | k` and `p | (m - 1) / p + 1`; it also records that
`m - 1` is squarefree. Thus `p^2` does not divide `m - 1`.

This DOI-bearing secondary source attests the literature statement. It does
not transfer Moree's author, year, title, or DOI to Moser's 1953 article. The
repository's Lean proof and its standalone block-decomposition and
sum-transport statements are not attributed to either paper.

## Search log

- 2026-09-05: Verified the article metadata as Pieter Moree, *Moser's
  mathemagical work on the equation 1^k + 2^k + ... + (m-1)^k = m^k*, *Rocky
  Mountain Journal of Mathematics* 43 (2013), no. 5, 1707-1737, DOI
  `10.1216/rmj-2013-43-5-1707`.
- 2026-09-05: Checked Theorem 2 and equations (5)-(7). They state the local
  divisibility restrictions above, exclude repeated prime factors of
  `m - 1`, and identify the proof as Moser's 1953 argument.
- 2026-09-05: Checked Moree's bibliography entry [29], which records L. Moser,
  *On the diophantine equation 1^n + 2^n + 3^n + ... + (m - 1)^n = m^n*,
  *Scripta Math.* 19 (1953), 84-88. Crossref, DataCite, OpenAlex, and Semantic
  Scholar yielded no DOI or arXiv identifier for that article, so this note
  uses Moree's DOI and attributes only the recorded theorem to Moser.

## Verified locator

- DOI: https://doi.org/10.1216/rmj-2013-43-5-1707
- Survey preprint: https://arxiv.org/abs/1011.2940
- Survey PDF: https://arxiv.org/pdf/1011.2940v2
