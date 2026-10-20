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


## Unconditional collision entropy

The same primary text, PDF p. 2, Section III, equation (8), defines
$H_\alpha(X)=(1-\alpha)^{-1}\log\sum_xp(x)^\alpha$ for an arbitrary
finite alphabet. With $\alpha=2$ and base-two logarithms this is
$H_{\mathrm{col}}(X)=-\log_2\sum_xp(x)^2$. For independent copies the
sum is their equality probability. The conditioned entropy choices of
(10)–(13) play no role in this definition.

[Actual pair energy, Section 23](../../docs/develop/theory/AURIC_FIB_ACTUAL_PAIR_ENERGY_OVERLAPPING_PROJECTIONS.md#23-原临界配对量的有限精度碰撞熵)
uses this standard entropy for a measurable address partition of the
actual matrix-word law. Its packing constant, original self-spin sum and
recovery-memory implication are applications derived in that volume;
no general entropy definition is claimed as new.

Shannon entropy near the history length alone does not imply the same
for collision entropy. Among $2^n$ equiprobable histories, merge
$M_n=\lfloor2^n/n\rfloor$ into one address and leave the others separate.
Writing $p=M_n2^{-n}$ gives

$$
H_{\mathrm{Sh}}=p\log_2(1/p)+(1-p)n=n-1+o(1),
\qquad
H_{\mathrm{col}}=-\log_2[p^2+(2^n-M_n)4^{-n}]
=2\log_2n+o(1).
$$

This elementary finite-law example concerns unrestricted partitions;
it makes no assertion that the repository's matrix-word partition has
this mass pattern. Jensen's inequality gives
$H_{\mathrm{col}}\le H_{\mathrm{Sh}}$ but supplies no reverse bound
at the strength needed for the critical pair estimate.
