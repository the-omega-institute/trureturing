---
bibkey: "ditzhaus2018detectability"
authors: "Marc Ditzhaus; Arnold Janssen"
year: 2018
title: "Detectability of nonparametric signals: higher criticism versus likelihood ratio"
doi: "10.1214/18-EJS1502"
url: "https://arxiv.org/abs/1709.07264v2"
claim: "Theorem 4.10 gives beta=1 log-likelihood-ratio limits: the null limit is the constant -1/2 at r=1 and -1 for r>1, while the alternative limit has a finite atom and mass at positive infinity; independent Bernoulli indicators give a random signal count."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Detectability of nonparametric signals: higher criticism versus likelihood ratio

Electronic Journal of Statistics 12(2) (2018). The inspected source is
arXiv:1709.07264v2, revised 7 August 2018, a 43-page PDF; v1 was submitted
21 September 2017. The journal title, authors, year, volume, issue and DOI
are corroborated by Crossref.

Section 1.1, PDF page 3, defines independent Bernoulli indicators for
signal occurrence. Their sum is a random count. In the extreme sparse
Gaussian model of §4.2, with occurrence probability `1/n`, that count
converges to Poisson(1). It is not fixed to one or to another prescribed
positive integer.

Theorem 4.10, PDF page 19, extends the Gaussian detection boundary to
`beta = 1`. At its signal parameter `r = 1`, the null **log-likelihood ratio**
converges to `-1/2`, so the likelihood ratio converges to `exp(-1/2)`; for `r > 1`
the corresponding limits are `-1` and `exp(-1)`. The theorem also gives
the alternative log-likelihood-ratio limit, including mass at positive infinity.
Its parameter `r` is the Gaussian logarithmic signal-strength parameter,
not the bounded parity-kernel amplitude.

Nontrivial alternative critical limits with finitely many expected signals
and loss of likelihood-ratio mean are therefore `literature-attested`. The theorem does
not supply an exact fixed-cardinality support law, a compensated Markov
kernel, or a full stationary path observation. For the parity construction,
the uniform comparison between a genuine multi-spike likelihood and the
product of single-spike likelihoods, followed by the fixed-cardinality
mixture calculation, is a separate model-specific `repo-derived`
argument. No global originality conclusion follows from this distinction.
