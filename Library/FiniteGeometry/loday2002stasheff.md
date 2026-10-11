---
bibkey: loday2002stasheff
authors: Jean-Louis Loday
year: 2002
title: "Realization of the Stasheff polytope"
doi: null
url: https://arxiv.org/abs/math/0212126v1
claim: "Products of left and right child leaf counts give Stasheff-polytope coordinates; consecutive block sums have the triangular lower bound, with equality on the corresponding complete subtree."
strata_touched:
  - D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval
license: citation-only
triage: anchor
---

# Ancestor coordinates and consecutive blocks

## Verified locator

Jean-Louis Loday, *Realization of the Stasheff polytope*, arXiv:math/0212126v1.

Versioned abstract: https://arxiv.org/abs/math/0212126v1

Original source: https://arxiv.org/src/math/0212126v1

The original source archive has SHA-256
`4e150ff25f6201c90f141dd990bcfd87e3427cbb9aa39a3b59e6a554c712f791`.
Its `spXXX.tex` defines the coordinates in lines 795-808, proves their total
in Lemma 2.5 (lines 950-973), and treats admissible proper consecutive blocks
in Proposition 2.6 (lines 976-1003).

For a native tree with m leaves and a one-based interval [a,b], the correspondence
is n=m-1, r=a-1, d=b-a, x_i=A_i, and S(d)=choose(b-a+1,2). Loday numbers leaves
from zero and internal vertices from one. The inorder vertex between leaves
i-1 and i contributes the product of its two child leaf counts. The native
coordinate list is the left list, the root product, and the right list.

Proposition 2.6 identifies proper-block equality with the corresponding subtree
refinement and gives strict inequality otherwise. Its proper-block formulation
alone does not cover a singleton interval, the full-tree interval, or a one-leaf
tree. The native theorem includes all of these: an empty gap sum is zero, a
singleton is a leaf occurrence, and the full interval is the root occurrence.
Boolean labels can repeat because the coordinates depend only on the ordered
shape; subtree occurrences retain their actual Boolean addresses.

This is literature-attested classical provenance, not a novelty claim. No source
code or proof text is incorporated under a software license.
