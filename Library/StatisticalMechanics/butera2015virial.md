---
bibkey: butera2015virial
authors: Paolo Butera; Paul Federbush; Mario Pernici
year: 2015
title: "Positivity of the virial coefficients in lattice dimer models and upper bounds on the number of matchings on graphs"
doi: 10.1016/j.physa.2015.05.106
url: https://arxiv.org/abs/1502.06734v2
claim: "For a finite regular graph with N(i) the number of configurations of i dimers (i-edge matchings) and nu the matching number, the paper argues that the bounds Delta^k ln(i! N(i)) <= 0 for k = 2, ..., nu and i = 0, ..., nu - k (Eq. (1), with Delta the forward difference) correspond to the positivity of the virial coefficients, reports tests on lattice graphs and on regular biconnected graphs, and asks whether these bounds for k <= 4 always hold for regular biconnected graphs."
strata_touched:
  - D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation
license: citation-only
triage: anchor
---

# Butera–Federbush–Pernici, virial positivity and matchings on graphs

P. Butera, P. Federbush, M. Pernici, Physica A 437 (2015) 278–294,
arXiv:1502.06734v2 (cond-mat.stat-mech). Quotations are from the arXiv v2
source.

Abstract:

> The validity of the bounds $\Delta^k {\rm \ln}(i! N(i)) \le 0$ for $k \ge
> 2$, where $N(i)$ is the number of configurations of $i$ dimers on
> the graph and $\Delta$ is the forward difference operator, is shown
> to correspond to the positivity of the virial coefficients.

Introduction, before Eq. (1):

> Using the definition of the graph dimer entropy[\onlinecite{bfppos}],
> we argue that for a finite regular graph the bounds which correspond
> to the positivity of the virial coefficients $m_k$ for infinite regular lattices are

followed by Eq. (1), $\Delta^k {\rm \ln}(i! N(i)) \le 0$, and

> with $k=2,...,\nu$ and $i=0,...,\nu-k$, where $\nu$ is the matching
> number of $G$, i.e. the maximum number of pairwise disjoint edges of
> $G$.

Section IV B, after the tests on finite lattices with open boundary
conditions:

> For all the graphs examined in this section, Eq. (\ref{Delta0}) is
> satisfied for $k \le 4$. It would be interesting to know whether these
> bounds, Eq. (\ref{Delta0}) for $k \le 4$, are always satisfied for
> regular biconnected graphs.

The Conclusions note that for $k=2$ the bounds follow from the
Heilmann–Lieb inequality. Sections IV C and IV D test Eq. (1) on regular
biconnected bipartite and non-bipartite graphs and report violations only
for $k\ge5$.

The encoding reads $N(i)$ as the number of $i$-edge matchings of $K_n$
all of whose edges are edges of $G$, $\nu$ as the supremum of the $i$ with
$N(i)>0$, $\Delta$ as `fwdDiff 1`, and "regular biconnected" as: every
vertex has the same degree, $G$ is connected, and $G-v$ is connected for
every vertex $v$.

## Verified locator

- DOI: https://doi.org/10.1016/j.physa.2015.05.106 (Physica A 437 (2015)
  278–294).
- URL: https://arxiv.org/abs/1502.06734v2 (the latest version, 2015-05-20;
  source `virial8j_c3b_arXiv.tex`, md5 `26db1bd9f13d1a867af773dc8058ff37`):
  abstract (l. 56–60), Heilmann–Lieb sentence (l. 105–107), Eq. (1)
  (l. 120–128), the question (l. 1010–1013), tests on bipartite and
  non-bipartite graphs (l. 1017–1148), Conclusions (l. 1461–1480).
