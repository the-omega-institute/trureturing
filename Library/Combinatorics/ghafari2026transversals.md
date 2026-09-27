---
bibkey: ghafari2026transversals
authors: Afsane Ghafari, Ian M. Wanless
year: 2026
title: Latin Squares whose transversals intersect in unusual ways
doi: 10.48550/arXiv.2607.17547
url: https://arxiv.org/abs/2607.17547v1
claim: Equation (7) defines the Latin square H; Lemma 8 proves pairwise intersection of its transversals for k >= 9, and Section 3 establishes no pinned entry for 9 <= k <= 2500.
strata_touched: []
license: citation-only
triage: anchor
---

# Ghafari–Wanless H family: source and scope

The primary source is arXiv:2607.17547v1, submitted 20 July 2026.
The version-specific TeX source is available from
https://arxiv.org/src/2607.17547v1. Its `TransAlgo.tex` has SHA-256
`fbc03bc2e8a4ebf0c0aac4e76c27fc1ead40c81f0dbee379720cfe2fc80d3a3e`.

The following assertions are `literature-attested`:

- Section 3, equation (7), source label `Structuretwo`, defines H of
  order n = 4k and asserts that it is Latin. Its cases have priority in
  their printed order. The source initially defines this family for
  k >= 4; the manuscript uses only k >= 9.
- Lemma 5, source label `l:Delta`, gives the transversal Delta-sum
  congruence n/2 modulo n when n is even.
- Lemma 8, source label `zeromodfour`, proves that H has no pair of
  disjoint transversals when k >= 9. Its row bounds force every
  transversal to contain at least two of (1,1,5), (6,5,14), (11,9,23).
  Although the proof introduces its aim using the words “exactly two”,
  the concluding argument establishes “at least two”; that is the
  assertion used in the manuscript.
- The paragraph near the end of Section 3, immediately before Section 4,
  reports three transversals with empty total intersection for every
  H of order 4k with 9 <= k <= 2500. These finite cases are prior art.
  Theorem 6 establishes the larger finite range n = 28 and even
  32 <= n <= 10000, using both families and separate small constructions.
- Conjecture 3 asks for a Latin square with pairwise-intersecting
  transversals and no pinned entry at every even order n >= 28.
  In particular, its order-30 existence assertion is not among the
  finite cases of Theorem 6.

The explicit uniform formulas and proofs in
[LATIN_H_TRANSVERSALS.md](../../docs/develop/theory/LATIN_H_TRANSVERSALS.md)
are `repo-derived` ordinary mathematics. Their Latinness premise is the
source assertion accompanying equation (7). The construction supplies
three transversals for every k >= 9; the source's finite search result
is not used as a premise of that uniform construction. There is no Lean
consumer associated with this note. Full Conjecture 3 remains unresolved
by this H-family result; neither a result for G nor an order-30 square
with the conjectured properties follows from it.

As of 21 September 2026, the arXiv version record lists only v1. The
bounded arXiv query `all:"transversals" AND (au:Ghafari OR au:Wanless)`
returns 13 entries, with this paper the most recent; OpenAlex work
W7169882857 has zero indexed citing works, also zero in its direct
citing-work query. No later uniform construction for this same H family
was located in those results. These restricted indexes do not establish
novelty or exclude other authors, unpublished work, or unindexed sources.
