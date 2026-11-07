---
bibkey: goddardkuenzelmelville2022wellhued
authors: Wayne Goddard, Kirsti Kuenzel, Eileen Melville
year: 2022
title: "Well-hued graphs"
doi: 10.1016/j.dam.2022.06.010
url: https://people.computing.clemson.edu/~goddard/papers/wellhued.pdf
claim: "Lemma 6 and Theorem 10 classify well-hued rook graphs and supply the maximal-colorability obstruction at K3 box K3."
strata_touched:
  - D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation
license: citation-only
triage: anchor
---

# Well-hued rook graphs

## Verified locator

DOI: https://doi.org/10.1016/j.dam.2022.06.010

Author PDF: https://people.computing.clemson.edu/~goddard/papers/wellhued.pdf

Published in *Discrete Applied Mathematics* 320 (2022), pages 370–380.
Section 3.5 of the author PDF contains Lemma 6 and Theorem 10.

For positive integers `n >= m`, Lemma 6 states that the Cartesian product
`K_m box K_n` has equal orders for its maximal induced `j`-colorable
subgraphs exactly when `j >= m` or `j <= n-m+1`. Its proof constructs a
smaller maximal-colorability obstruction in the intervening range.
Theorem 10 concludes that this rook graph is well-hued exactly when
`n >= 2(m-1)`.

At `m=n=3`, the obstruction occurs for two colors. A four-cycle plus the
opposite isolated cell has order five, whereas the complementary-diagonal
six-cycle has order six; both are maximal induced bipartite sets. The Lean
module checks these concrete facts directly. Their mathematical structure
and the failure of well-huedness are attributed to this paper, rather than
claimed as a new rook-graph classification. The separate connection to
the 2025 Conjecture 2 is the target of the refutation module.

For complete factors, K_m box K_n is exactly the two-coordinate mixed-alphabet Hamming graph with alphabet sizes m and n: an edge changes exactly one coordinate. Its coordinate lines are cliques, and its independent sets are partial permutation sets. At m=n=3 and two colors, Lemma 6 constructs J-prime from the two-by-two subboard and D from the opposite cell; their union is the five-vertex set S used by the certificate, after relabeling coordinates by 0,1,2. The off-diagonal six-cycle T is the other certified maximal two-colorable set. Each set partitions into two independent classes, and each omitted cell completes a coordinate-line 3-clique. Thus the cited Cartesian-product results directly concern partitions and induced colorability maximality in this Hamming graph. These are independent-set partitions, rather than partitions into coordinate-line cliques.

This is an original citation summary. The author PDF supplies no general
reuse license used here; no source code, figures or proof text is copied.
