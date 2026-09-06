---
bibkey: vemuri2019domination
authors: Harish Vemuri
year: 2019
title: Domination in Direct Products of Complete Graphs
doi: 10.48550/arXiv.1908.02445
claim: "Domination numbers of direct products of complete graphs have known lower bounds; Theorem 1.1 cites Mekis's bound gamma >= t+1 for t >= 4 factors."
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation
license: citation-only
triage: anchor
---

# Known product-graph ingredient

Checked https://arxiv.org/html/1908.02445v1 on 2026-09-07 Asia/Singapore.
The introduction, Theorem 1.1, and Theorem 1.2 were read. Theorem 1.1
attributes to Mekis (2010), Theorem 2.1, the lower bound gamma >= t+1
for a direct product of t >= 4 complete graphs with factor sizes at least
two, with equality when the smallest factor is at least t+1. Theorem 1.2
cites stronger results of Defant and Iyer (2018).

The repository only needs gamma >= t when each factor has at least t
vertices. Its diagonal argument is elementary and is not claimed as new
mathematics. The bound, connectedness and degree counting are formalized
for the existing Mathlib SimpleGraph type. No corresponding Lean theorem
was found in the ordered D5, pinned Mathlib and ecosystem searches.

The repository parameterization is t=r+1 factors of size 2*t+1. The initial
revised preregistration used r factors of size 2*r; the shift removes zero
coordinate and subtraction bookkeeping and preserves the same density
and unbounded-domination argument. This implementation adjustment is
disclosed after the probes, not represented as an earlier preregistration.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.1908.02445. Independently resolved and
checked on 2026-09-07 Asia/Singapore against
https://arxiv.org/html/1908.02445v1 (2019-08-07), Introduction,
Theorems 1.1 and 1.2. Theorem 1.1 attributes the bound gamma >= t+1 for
t >= 4 complete factors of size at least two to Mekis (2010), Theorem 2.1;
Theorem 1.2 cites Defant and Iyer. This locates established product-graph
ingredients, not the repository's cover refutation or a priority claim.
