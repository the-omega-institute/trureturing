---
bibkey: "mukherjee2015binary"
authors: "Rajarshi Mukherjee; Natesh S. Pillai; Xihong Lin"
year: 2015
title: "Hypothesis testing for high-dimensional sparse binary regression"
doi: "10.1214/14-AOS1279"
url: "https://arxiv.org/abs/1308.0764v3"
claim: "For independent binomial coordinates with denominator much larger than log dimension, Theorems 6.8(2) and 6.10(2) give the sparse detection boundary and an attaining Higher Criticism test."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Hypothesis testing for high-dimensional sparse binary regression

The Annals of Statistics 43(1), 352–381 (2015), DOI 10.1214/14-AOS1279.
The inspected source is the 32-page arXiv:1308.0764v3 PDF, revised
5 March 2015; its first page gives the journal pagination and DOI.
Crossref corroborates the title, authors, year, journal, volume and issue.

Equation (6.1), PDF page 17, defines independent coordinates
`Y_j ~ Bin(r, 1/2 + nu_j)`. The alternative in (6.2) has sparse nonzero
shifts with absolute magnitude at least `Delta`; the signs may differ.
Remark 6.2, page 18, specifies a uniform fixed-size support and independent
random signs for the lower-bound prior.

Equation (6.4), page 21, gives
`rho_binomial(alpha) = (alpha - 1/2)/4` for `1/2 < alpha < 3/4`, and
`(1 - sqrt(1-alpha))^2/4` above that range. Theorems 6.8(2) and 6.10(2),
pages 21–22, assume `r >> log p`, `k = p^(1-alpha)` and
`Delta = sqrt(2 t log p / r)`. Below the stated boundary all tests are
asymptotically powerless; above it their Higher Criticism test is powerful.

To compare with parity sign rows, map their denominator `r` to the number
`m` of samples per row, `p` to `M`, `alpha` to `beta`, and `Delta` to half
the parity amplitude. Their strength `t` is then one quarter of the
parity parameter `rho = m * amplitude^2 / (2 log M)`. The resulting
boundary is the classical sparse-testing curve; it is
`literature-attested`, not a new curve derived by the parity model.

A lower bound for the paper's larger signed alternative does not by itself
prove a lower bound for the positive fixed-support subclass. The parity
argument supplies its own positive-support truncated likelihood calculation,
removes the compensating background in total variation, and compares the
actual forward and reversed trajectory laws with row samples. Those
connections, and the resulting direction experiment, are `repo-derived`;
they do not assert a new general binomial detection theorem.
