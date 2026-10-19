---
bibkey: liu2026binaryentropyhardness
authors: Y. Liu
year: 2026
title: "Computational hardness of estimating quantum entropies via binary entropy bounds"
doi: 10.4230/LIPIcs.STACS.2026.66
url: https://arxiv.org/abs/2601.03734v2
claim: "Section 1.4(b) asks whether (H_alpha(x)/ln(2))^(2/alpha) is non-decreasing in alpha for every binary probability x."
strata_touched:
  - D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation
license: citation-only
triage: anchor
---

# Liu on powered binary Renyi entropy

Y. Liu, *Computational hardness of estimating quantum entropies via binary
entropy bounds*, STACS 2026, LIPIcs 364, article 66.

## Verified locator

- DOI: https://doi.org/10.4230/LIPIcs.STACS.2026.66
- Author version: https://arxiv.org/abs/2601.03734v2
- Section 1.4(b), second open question; the binary-entropy definition in Section 2.1.

The binary Renyi entropy is
$H_\alpha(x)=\log(x^\alpha+(1-x)^\alpha)/(1-\alpha)$ for $x\in[0,1]$
and $\alpha\ne1$. The question concerns monotonicity of
$(H_\alpha(x)/\log 2)^{2/\alpha}$ in the positive order $\alpha$.

The counterexample $x=1/17$, $a=1/4$, $b=1/2$ gives
$H_a(x)=(4/3)(\log 3-\log 17/4)$ and $H_b(x)=\log(25/17)$.
The normalized entropies satisfy $H_a(x)/\log 2>3/4$ and
$0<H_b(x)/\log 2<9/16$, so the powered entropy strictly decreases.
