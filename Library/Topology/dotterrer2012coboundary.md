---
bibkey: dotterrer2012coboundary
authors: Dominic Dotterrer, Matthew Kahle
year: 2012
title: "Coboundary expanders"
doi: 10.1142/S1793525312500197
url: https://arxiv.org/abs/1012.5316v2
claim: "Proposition 5.5 gives the cross-polytope coboundary expansion lower bound 2(n-k-1)/(k+2), hence 2R <= 3T for n=3 and k=1 in support-count norms."
strata_touched:
  - D5/S3/Combinatorics/Graph/TripartiteH1Repair
license: citation-only
triage: anchor
---

# Cross-polytope coboundary expansion

## Verified locator

DOI: 10.1142/S1793525312500197

URL: https://arxiv.org/abs/1012.5316v2

- Locator: Section 2 defines the cochain norm by support size.
- Locator: Proposition 5.5 gives the cross-polytope boundary expansion bound
  $2(n-k-1)/(k+2)$; at $n=3$, $k=1$ this is $T/R\geq2/3$.

Dotterrer and Kahle, *Coboundary expanders*, Proposition 5.5, proves a
coboundary expansion estimate for the cross-polytope boundary. Their Section 2
defines the cochain norm as support size. At three opposite vertex pairs and
degree one, its bound is $T/R\geq2/3$, equivalently $2R\leq3T$ for raw edge
and triangle counts. Dividing each count by the number of edges or triangles
would give a different normalized ratio. The proposition supplies the
published upper bound. The three-edge antipodal equality witness in the
repository is a separate, directly formalized construction.
