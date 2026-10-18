---
bibkey: hirche2020renyibounds
authors: Christoph Hirche
year: 2020
title: "Rényi Bounds on Information Combining"
doi: null
url: https://arxiv.org/abs/2004.14408v1
claim: "Conjecture IV.18 asks for a threshold 1 < alpha_hat < 1.3863 giving separate convexity below it and separate concavity for alpha at least two."
strata_touched:
  - D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity
license: citation-only
triage: anchor
---

# Rényi bounds on information combining

The source is C. Hirche, “Rényi Bounds on Information Combining”, ISIT 2020,
arXiv:2004.14408v1, Conjecture IV.18. The conjecture scope and source locator
are supplied by the preregistration
[#18704](https://github.com/the-omega-institute/trureturing/issues/18704).
This note records that supplied scope; it does not assert an independent
literature or priority search.

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
