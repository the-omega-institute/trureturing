---
bibkey: liu2026binaryentropybounds
authors: Yupan Liu
year: 2026
title: "Computational hardness of estimating quantum entropies via binary entropy bounds"
doi: 10.4230/LIPIcs.STACS.2026.66
url: https://arxiv.org/abs/2601.03734v2
claim: "With the binary Renyi entropy H^R_alpha(x) = ln(x^alpha + (1-x)^alpha)/(1-alpha), the paper asks whether (H^R_alpha(x)/ln 2)^{2/alpha} is monotonically non-decreasing in alpha for every fixed x in [0,1], as suggested by numerical evidence and generalizing its comparison with order 2."
strata_touched:
  - D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation
license: citation-only
triage: anchor
---

# Computational hardness of estimating quantum entropies via binary entropy bounds

Yupan Liu, arXiv:2601.03734v2 (quant-ph), 2026-04-07; v1 2026-01-07; STACS 2026, LIPIcs 364, article 66. Quotations are from the v2 TeX source.

The binary entropies (Section 2.1):

> The $q$-Tsallis binary entropy $\Hq(x)$ and the $\alpha$-R\'enyi binary entropy $\Halpha(x)$ are defined by: for any $x\in[0,1]$,
> \Halpha(x) &\coloneq\frac{\ln\rbra*{x^\alpha + (1-x)^{\alpha}}}{1-\alpha}.

The open question (Section 1.4(b)):

> Can the inequalities in \Cref{table:Rank2RenyiQEA-hardness} be tightened? For instance, is it possible to prove that $\rbra[\big]{\frac{\Halpha(x)}{\ln(2)}}^{2/\alpha}$ is monotonically non-decreasing in $\alpha$ for all fixed $x\in[0,1]$, as suggested by numerical evidence and as a generalization of \Cref{thm:Renyi-binary-entropy-upper-bound-0leAle2}?

## Verified locator

- DOI: https://doi.org/10.4230/LIPIcs.STACS.2026.66 (STACS 2026, LIPIcs 364, article 66; the DOI resolves to the Dagstuhl landing page with this title; the published text was not read).
- URL: https://arxiv.org/abs/2601.03734v2 (v2, 2026-04-07; v1, 2026-01-07; source `entropyHardness.tex`, md5 `707b5497956656274c317b37f9f9f590`): the open question (l. 470) and the binary entropies (l. 494–497).
