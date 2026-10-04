---
bibkey: yurischev2017extremal
authors: M. A. Yurischev
year: 2017
title: "Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states"
doi: 10.1007/s11128-017-1701-0
url: https://arxiv.org/abs/1702.03728v3
claim: "For two-qubit X states the conditional entropy is written through f_1(x) = -h_2((1+p_2 x)/2, (1-p_2 x)/2) + h_4((1+p_2 x + sqrt(r_1))/4, (1+p_2 x - sqrt(r_1))/4, (1-p_2 x + sqrt(r_2))/4, (1-p_2 x - sqrt(r_2))/4) on x in [0,1] (Eq. (A1)), with r_1 = (p_1 + p_5 x)^2 + 4 w^2 (1 - x^2), r_2 = (p_1 - p_5 x)^2 + 4 w^2 (1 - x^2), w = (|p_3+p_4| + |p_3-p_4|)/4 and Shannon entropies in bits. Section 2 supposes the unimodal property of the conditional entropy, and the Appendix conjectures that f_1 and f_2 have at most one local extremum in (0,1) for every choice of parameters with nonnegative Shannon arguments. Weak unimodality on [a,b] means weak increase up to some x_m in [a,b] and weak decrease after it, with the analogous form for the minimum."
strata_touched:
  - D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation
license: citation-only
triage: anchor
---

# Extremal properties of conditional entropy and quantum discord for XXZ, symmetric quantum states

M. A. Yurischev, Quantum Inf. Process. 16, 249 (2017); arXiv:1702.03728v3.
Quotations are from the arXiv v3 source.

The function of Eq. (A1):

> $f_1(x;p_1,p_2,p_3,p_4,p_5)=-h_2\bigl(\frac{1+p_2x}{2},\frac{1-p_2x}{2}\bigr)+h_4\bigl(\frac{1+p_2x+\sqrt{r_1}}{4},\frac{1+p_2x-\sqrt{r_1}}{4},\frac{1-p_2x+\sqrt{r_2}}{4},\frac{1-p_2x-\sqrt{r_2}}{4}\bigr)$

> with $r_{1,2}=(p_1\pm p_5x)^2+4w^2(1-x^2)$ and $w=(|p_3+p_4|+|p_3-p_4|)/4$.

Here $h_2$ and $h_4$ are "the binary and quaternary entropy Shannon
functions; $0\le h_2\le1$ bit and $0\le h_4\le2$ bits", and $f_1$
corresponds to the conditional entropy of an X state.

The definition of weak unimodality (Appendix):

> A function $f(x)$ is a weakly unimodal function in the interval $[a,b]$ if there exists a value $x_m\in[a,b]$ for which it is weakly monotonically increasing for $x\le x_m$ and weakly monotonically decreasing for $x\ge x_m$. […] Analogous definitions are given for the minimum.

The hypothesis (Section 2):

> On the other hand, we suppose the unimodal property for the function $S_{cond}(\theta)$ (see Appendix). So, if the unimodality hypothesis is valid the only possibility (except the trivial case $S_{cond}(\theta)=const$) for a single local extremum (minimum or maximum) to appear or disappear inside the open interval by continuous varying the parameters defining the X state is the doubling the extremun at the ends of interval $[0,\pi/2]$.

The conjecture (Appendix):

> The functions $f_1(x)$ and $f_2(x)$ for every choice of parameters $p_1,\ldots,p_5$ for which all arguments of Shannon functions are non-negative can have at most only one local extremum (minimum or maximum) in the open interval $x\in(0,1)$. […] It is required to prove or refute this proposition.

The encoding writes $h_2$ and $h_4$ with `Real.negMulLog` divided by
`Real.log 2`, takes the parameters' admissible set to be those $p$ whose
Shannon arguments are nonnegative for every $x\in[0,1]$, and states the
hypothesis for $f_1$ as weak unimodality on $[0,1]$ in the maximum form or
the minimum form.

## Verified locator

- DOI: https://doi.org/10.1007/s11128-017-1701-0 (Quantum Inf. Process. 16,
  249 (2017); journal reference from the arXiv record, DOI from Crossref).
- URL: https://arxiv.org/abs/1702.03728v3 (v3, 2017-04-14, the latest
  version; source `paper.TEX`, md5 `a2ac0c1ac88d0d7ce84e27b6e45f89f4`):
  abstract (l. 39–58), the hypothesis (l. 169–175), strong and weak
  unimodality (l. 1310–1326), Eq. (A1) with $r_{1,2}$ and $w$
  (l. 1340–1361), the Shannon functions (l. 1388–1395) and the conjecture
  (l. 1398–1406).
