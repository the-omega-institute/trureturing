---
bibkey: meerweeks2024boundedmoments
authors: David J. Meer; Eric R. Weeks
year: 2024
title: "Bounded distributions place limits on skewness and larger moments"
doi: 10.1371/journal.pone.0297862
url: https://arxiv.org/abs/2308.05006v2
claim: "The paper proves lower bounds on the skewness of distributions bounded on one side in terms of the coefficient of variation, derives the corresponding bidisperse limits for all standardized moments D_n, and conjectures that the bidisperse limit D_5 ≥ z^3 - z + z^(-1) - z^(-3) holds for every distribution bounded from below (and its analogue for distributions bounded from above)."
strata_touched:
  - D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit
license: citation-only
triage: anchor
---

# Bounded distributions place limits on skewness and larger moments

D. J. Meer and E. R. Weeks, arXiv:2308.05006v2 [stat.AP, cond-mat.stat-mech]; PLOS ONE 19, e0297862 (2024). Quotations are from the v2 TeX source.

The normalization for distributions bounded from below:

> Now consider the general case of a distribution $P(x)$ bounded by $x_{\rm min}$ from below and with a mean $\mu$ which might be zero. Let us assume $P(x)$ has a nontrivial domain, which is to say, it is not a distribution which is only nonzero at one value (which would thus be $\sigma=0, D_3=0$). $\delta = \sigma/(\mu - x_{\rm min}).$

(the display is written inline here).

The conjecture:

> One can immediately put in a value for $a$ of interest and get a potential limit of $D_n$. For example, for distributions bounded from below by $x_{\rm min}$ we conjecture $D_5 \geq D_{5,{\rm min}} = z^3 - z^1 + z^{-1} - z^{-3}$ with $z = \delta / (1 - x_{\rm min}/\mu)$ as above. As with $D_3$, our conjectured $D_{5,{\rm max}}$ is a similar equation using $z = \delta / (x_{\rm max}/\mu - 1)$.

(the display is written inline here).

## Verified locator

Source: https://arxiv.org/abs/2308.05006v2
- URL: https://arxiv.org/abs/2308.05006v2 (source `plos_latex_template.tex`, md5 `4452c28a26c7a76c87642af46fe0c8a9`):
  - the moments $m_n$ and $D_n$, l. 228–236;
  - the bounded-below and bounded-above normalizations, l. 396–408;
  - Eq. `DNlimits` and the conjecture, l. 496–510;
  - the remark on counterexamples for $n=5$, l. 532.
- DOI: 10.1371/journal.pone.0297862 (https://doi.org/10.1371/journal.pone.0297862; Crossref lists PLOS ONE, volume 19, article e0297862, published 9 February 2024).
