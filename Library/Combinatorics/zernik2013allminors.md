---
bibkey: zernik2013allminors
authors: Amitai Zernik
year: 2013
title: "Taylor expansion proof of the matrix tree theorem — part II"
doi: null
url: https://arxiv.org/abs/1308.2160v1
claim: "Definitions 1 and 4, Theorem 2 and Lemma 5: complementary minors of column-sum-zero matrices are signed sums of directed spanning forests, with component-induced ascending root matching."
strata_touched:
  - D5/S3/Combinatorics/Graph/DirectedAllMinorsMatrixTree
license: citation-only
triage: anchor
---

# Directed all-minors matrix-tree identity

The reference is arXiv:1308.2160v1, pages 1–5. Rows indexed by W and columns indexed by U are deleted, with both complements in increasing order. Each component of a forest has exactly one U vertex and one W vertex, and its arrows point away from U. The arrow i to j has weight Mij. The sign is the component-induced bijection sign in increasing root coordinates, multiplied by (-1) raised to n + k + the sums of both root labels.

Zernik's proof compares derivatives over the real vector space of column-sum-zero matrices. The repository theorem instead expands by native determinant multilinearity, proves the integer incidence coefficient combinatorially, and maps that coefficient into an arbitrary commutative ring. It neither lifts arbitrary ring-valued matrices to integer matrices nor transports the vanishing of real derivatives to positive characteristic. Zero rings, signed and zero weights, overlapping roots, nonprincipal minors, arbitrary size, and the empty minor are included.

The graph and matching clauses are defined independently of determinants. Parent choices are reindexed by their actual directed edges. Integer column independence excludes every edge that closes an existing undirected path, including reversed duplicate edges. Tree edge counts give one U root per component; equal root cardinalities and the component-indicator nullrelation give one W mark. Unique rooted paths establish the arrow orientation. Integer depth-triangular determinants, actual path column operations, and the exact ascending shuffle sign supply the coefficient.

## Verified locator

- URL: https://arxiv.org/abs/1308.2160v1
- Definition 1 and Theorem 2: page 1.
- Definition 4 and Lemma 5: page 2.
- Theorem 2 proof: pages 2–4.
- Lemma 5 proof and references: pages 4–5.

The forest identity and its signs are literature-attested; no mathematical originality is claimed.
