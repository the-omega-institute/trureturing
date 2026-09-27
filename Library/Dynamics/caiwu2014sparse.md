---
bibkey: "caiwu2014sparse"
authors: "T. Tony Cai; Yihong Wu"
year: 2014
title: "Optimal Detection of Sparse Mixtures Against a Given Null Distribution"
doi: "10.1109/TIT.2014.2304295"
url: "https://arxiv.org/abs/1211.2265v1"
claim: "The general independent sparse-mixture framework relates detection boundaries to likelihood-ratio behavior at null-tail scales; it supplies background, not a fixed-cardinality compensated Markov-path theorem."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Optimal Detection of Sparse Mixtures Against a Given Null Distribution

IEEE Transactions on Information Theory 60(4), 2217–2232 (April 2014),
DOI 10.1109/TIT.2014.2304295. Crossref corroborates the journal title,
authors, date, volume, issue, pagination and DOI. The journal full text
was unavailable through the checked routes; its proof text has not been
inspected, and no assertion below relies on a journal correction.

The inspected primary preprint is the 32-page arXiv:1211.2265v1,
dated 9 November 2012, titled *Optimal Detection For Sparse Mixtures*.
Its first page identifies that arXiv version and date. The rendered
manuscript also displays 3 April 2022; the corresponding source file
`Detection-110812-arxiv.tex` contains the literal `\date{\today}`.
That displayed compilation date is not the preprint's version date.

The abstract, introduction and Section 3 relate sparse-mixture detection
to the behavior of a single-coordinate log-likelihood ratio at null-tail
scales. The main formulation, equation (10), compares independent samples
from `Q_n` against independent samples from
`(1 - epsilon_n) Q_n + epsilon_n G_n`. The paper develops general
non-Gaussian detection boundaries and Higher Criticism results. This
likelihood-ratio and tail-scale framework is `literature-attested`.

There is a source ambiguity in the inspected preprint's Theorem 3
(PDF page 11, equations (40)–(43)): it defines `F_n` and `z_n` as the CDF
and quantile function of `G_n`, whereas the following explanation calls
for null quantiles, and its proof (pages 25–26, equation (98)) represents
`W_n ~ Q_n` using `z_n(U)`. The source TeX contains the same `G_n`
definition. This note neither silently replaces that symbol nor invokes
the ambiguous displayed boundary formula as an exact theorem.

The parity-kernel argument cites the general framework as background and
derives its own compound-Poisson tail rates and scalar optimization.
Its positive support has a fixed cardinality and is held constant over
all observations. Its actual forward and reverse path laws are stationary
Markov laws with a compensating background. The independent contamination
prior above supplies neither their joint row-count approximation nor their
truncated overlap moments. Those connections require the separate
`repo-derived` finite-rank transfer and compensated-likelihood calculations.
No claim of worldwide originality, parameter adaptation, or equivalence
of the full pair and path experiments follows from this distinction.
