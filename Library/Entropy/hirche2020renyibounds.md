---
bibkey: hirche2020renyibounds
authors: Christoph Hirche
year: 2020
title: "Rényi Bounds on Information Combining"
doi: 10.48550/arXiv.2004.14408
url: https://arxiv.org/abs/2004.14408v1
claim: "Conjectures IV.6 and IV.18 ask for separate convexity and concavity thresholds for binary Arimoto and Cachin Rényi information combining."
strata_touched:
  - D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity
  - D5/S3/Entropy/RenyiCombining/HircheArimotoCombining
license: citation-only
triage: anchor
---

# Rényi bounds on information combining

The source is C. Hirche, “Rényi Bounds on Information Combining”, ISIT 2020,
arXiv:2004.14408v1, Eq. (23); §IV-A, Eq. (47), Conjecture IV.6;
and §IV-D, Conjecture IV.18, Eq. (88).
This note does not assert an independent literature or priority search.

## Locator

DOI: 10.48550/arXiv.2004.14408
Source: https://arxiv.org/abs/2004.14408v1
Eq. (23); §IV-A, Eq. (47), Conjecture IV.6;
§IV-D, Conjecture IV.18, Eq. (88).

## Arimoto information combining

Equation (23) defines
$K_\alpha^A(X\mid Y)=e^{((1-\alpha)/\alpha)H_\alpha^A(X\mid Y)}$.
For binary $X\sim\{p,1-p\}$, its coordinate is

$$
k_\alpha^A(p)=(p^\alpha+(1-p)^\alpha)^{1/\alpha},\qquad
p\star q=p+q-2pq.
$$

The source writes $(k_\alpha^A)^{-1}$ for the inverse branch on
$[0,1/2]$. Its coordinate domain is the closed interval with endpoints
$1$ and $\delta_\alpha=2^{(1-\alpha)/\alpha}$; equivalently,
$I_\alpha=[\min(1,\delta_\alpha),\max(1,\delta_\alpha)]$.
The implementation specifies this source inverse using `Function.invFunOn`.
Equation (47) is the combining expression

$$
k_\alpha^A\bigl((k_\alpha^A)^{-1}(x)\star(k_\alpha^A)^{-1}(y)\bigr).
$$

Conjecture IV.6 states: “There exists a value $1 < \hat\alpha < 1.5783$,
such that” this expression “is convex for $0 < \alpha < 1$ and concave
for $1 < \alpha \le \hat\alpha$.” The assertion is separate in each
coordinate on $I_\alpha$. The order $\alpha=1$ is excluded.

The hyperbolic elasticity and its analytic monotonicity certificate are
repository proof constructions, rather than definitions or results
attributed to this source.

## Cachin information combining

Conjecture IV.18 states verbatim: “There exists a value
$1 < \hat\alpha < 1.3863$, such that
$h_\alpha(h_\alpha^{-1}(x) \ast h_\alpha^{-1}(y))$ is convex for
$0 < \alpha < \hat\alpha$ and concave for $\alpha \ge 2$.”

For real $\alpha>0$, use natural logarithms and real powers. At
$\alpha=1$, put $h_1(p)=\operatorname{binEntropy}(p)$, the binary Shannon
entropy; at the other orders use:

$$
h_\alpha(p)=\frac{\log(p^\alpha+(1-p)^\alpha)}{1-\alpha},\qquad
p\star q=p+q-2pq.
$$

The inverse $h_\alpha^{-1}$ is the branch from $[0,\log2]$ to $[0,1/2]$.
For every $y\in[0,\log2]$, the source asks for convexity below its threshold
and concavity at orders at least two on $[0,\log2]$ of
$x\mapsto h_\alpha(h_\alpha^{-1}(x)\star h_\alpha^{-1}(y))$.
Both clauses include the entropy endpoints; the concavity clause includes $\alpha=2$.
