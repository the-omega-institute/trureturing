---
bibkey: cao2026sizeindependent
authors: Shen Cao; Xingjian Zhang; Fei Shi; Qi Zhao
year: 2026
title: "Size-Independent Robustness in Multipartite Bell Self-Testing"
doi: 10.48550/arXiv.2608.30851
url: https://arxiv.org/abs/2608.30851v1
claim: "Non-negativity of the explicit five-term lambda expression on [0, kappa]^n for h = 1, 2 and n >= 6."
strata_touched:
  - D5/S3/QuantumBounds/MabkSelfTestingPositivity
license: citation-only
triage: anchor
---

# Size-Independent Robustness in Multipartite Bell Self-Testing

The Supplemental Material, “Efficient Verification of Optimal Lower Bound”,
PDF p. 39, states:

> For $n \le 5$ this bound is already established analytically [20, 23]; for
> $n \geq 6$ the two remaining cases ($h = 1, 2$) are an open conjecture
> supported by the numerical evidence above.

The TeX source is `content_aps/sm_numeric.tex`, lines 14–23 (the five-term
expression) and line 160 (the quoted sentence, with citation keys
`Kaniewski_2016,Jha_Singh_Pan_2026`). The expression is evaluated for
$\kappa=1-1/\sqrt2$, with the two complementary index blocks of cardinalities
$h$ and $d$. The source assumes $h\le d$ by symmetry; $n\ge6$ and
$h\in\{1,2\}$ imply this condition.

The Lean definition `lambdaA` preserves all five terms, including the full
product multiplied by $((1+\sqrt2)/\sqrt2)^n$ and the two square-root cross
terms. Indices `Fin n` correspond to the source's indices $1,\ldots,n$ by
adding one. The block `T` represents $\mathcal T_{\vec a}$ and its complement
represents $\mathcal P_{\vec a}$.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.30851
- URL: https://arxiv.org/abs/2608.30851v1
- Source: https://arxiv.org/e-print/2608.30851v1
- PDF: https://arxiv.org/pdf/2608.30851v1, p. 39.
