---
bibkey: hirche2020renyibounds
authors: Christoph Hirche
year: 2020
title: "Rényi Bounds on Information Combining"
doi: null
url: https://arxiv.org/abs/2004.14408v1
claim: "Conjecture IV.18 includes concavity of binary Cachin Renyi information combining in each entropy coordinate for real orders alpha at least two."
strata_touched:
  - D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity
license: citation-only
triage: anchor
---

# Rényi bounds on information combining

The source is C. Hirche, “Rényi Bounds on Information Combining”, ISIT 2020,
arXiv:2004.14408v1, Conjecture IV.18. The formalized clause and source locator
are supplied by the preregistration
[#18704](https://github.com/the-omega-institute/trureturing/issues/18704).
This note records that supplied scope; it does not assert an independent
literature or priority search.

For real $\alpha\ge2$, use natural logarithms and real powers:

$$
h_\alpha(p)=\frac{\log(p^\alpha+(1-p)^\alpha)}{1-\alpha},\qquad
p\star q=p+q-2pq.
$$

The inverse $h_\alpha^{-1}$ is the branch from $[0,\log2]$ to $[0,1/2]$.
For every $y\in[0,\log2]$, the target is concavity on $[0,\log2]$ of
$x\mapsto h_\alpha(h_\alpha^{-1}(x)\star h_\alpha^{-1}(y))$.
The target includes both entropy endpoints and the parameter $\alpha=2$.
