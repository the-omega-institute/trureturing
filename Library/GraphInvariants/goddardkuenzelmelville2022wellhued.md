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

This is an original citation summary. The author PDF supplies no general
reuse license used here; no source code, figures or proof text is copied.
