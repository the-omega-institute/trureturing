---
bibkey: bubbolonicaceres2026neighbourhood
authors: Daniela Bubboloni; José Cáceres
year: 2026
title: "The neighbourhood convexity"
doi: 10.48550/arXiv.2608.25912
url: https://arxiv.org/html/2608.25912v1
claim: "For a finite nonempty simple undirected graph, the paper defines neighbourhood convexity and conjectures that every upset of the neighbourhood preorder is neighbourhood-convex whenever the neighbourhood convexity is a convex geometry. Lemma 29(iii) already proves this for principal upsets; the conjecture concerns all upsets."
strata_touched:
  - D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets
license: citation-only
triage: anchor
---

# The neighbourhood convexity

Daniela Bubboloni and José Cáceres, arXiv:2608.25912v1, version published
2026-08-26. The versioned HTML is
https://arxiv.org/html/2608.25912v1. Its inspected SHA256 is
`f10465fb6352f039eecb0bebd801fd4b839c50b7154c1c36e91a1409632e24af`.
This note quotes and cites the source; it does not redistribute the paper.

Sections 2.1 and 2.2 fix a finite nonempty simple undirected graph and the
convex-geometry condition. Definitions 3, 5 and 9 and Proposition 12 give

- $B(x)=\{x\}\cup\{y:xy\in E\}$,
- $N(X)=\bigcap_{x\in X}B(x)$, with $N(\varnothing)=V$,
- $C=\{N(Y):Y\subseteq V\}\cup\{\varnothing\}$,
- $h(\varnothing)=\varnothing$ and $h(X)=N(N(X))$ for $X\ne\varnothing$,
- $\operatorname{ex}(K)=\{x\in K:K\setminus\{x\}\in C\}$.

The full geometry hypothesis is $h(\operatorname{ex}(K))=K$ for every
$K\in C$. Definition 28 orders vertices by $B(x)\subseteq B(y)$.
Lemma 29(iii) identifies the principal upset of $x$ with $N(N(\{x\}))$ and
proves that it is convex. Lemma 29(iv) proves that convex sets are upsets.
Neither is a proof of arbitrary union closure.

In “Conclusions and future lines of work,” in the paragraph beginning
“By exploring the connection with the neighbourhood preorder P(G),” the
explicit unnumbered conjecture is:

> We conjecture that, given a convex geometry (G,n), any upset in P(G) is an n-convex set, having checked it computationally for graphs up to 9 vertices.

The finite computations are author-reported and are not independently
verified here. The separate conjecture about extreme points is not this
assertion. The source's statement remains a conjecture in the cited version;
the project result is a separate proof, not a published settlement by the
original authors.
