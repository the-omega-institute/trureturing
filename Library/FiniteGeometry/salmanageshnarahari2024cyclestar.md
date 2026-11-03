---
bibkey: salmanageshnarahari2024cyclestar
authors: Umme Salma; H. M. Nagesh; Narahari N.
year: 2024
title: On edge irregularity strength of cycle-star graphs
doi: 10.22199/issn.0717-6279-5801
url: https://arxiv.org/abs/2405.12263v1
claim: "Conjecture 3.1 asserts es(CS_{k,n-k}) = ceil((n+1)/2) for k+1 <= n <= 2k-4 and es(CS_{k,n-k}) = n-k+2 for n >= 2k-3, whenever k >= 8 and n-k >= 1."
strata_touched:
  - D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.22199/issn.0717-6279-5801

Source: https://arxiv.org/abs/2405.12263v1

Proyecciones Journal of Mathematics 43(3), 725–741 (2024). The journal
definitions on printed pages 726–727 and Conjecture 3.1 on printed page 738
agree with arXiv v1. The quotations below preserve the source TeX.

## Labelings and edge weights

Section 1, printed page 726:

> A vertex labeling $\phi:V(G) \rightarrow \{1, 2,\ldots,k\}$ is called *$k$-labeling*. The weight of an edge $uv$ in $G$, written $w_{\phi}(uv)$, is the sum of the labels of end vertices $u$ and $v$, i.e., $w_{\phi}(uv)=\phi(u)+\phi(v)$. A vertex $k$-labeling of a graph $G$ is defined to be an *edge irregular $k$-labeling* of the graph $G$ if for every two different edges $u$ and $v$, $w_{\phi}(u) \neq w_{\phi}(v)$. The minimum $k$ for which the graph $G$ has an edge irregular $k$-labeling is called the *edge irregularity strength* of $G$, written $es(G)$.

Repeated vertex labels are permitted. Unordered edges, rather than their
orientations, must have distinct endpoint sums. A strength value includes
both attainment and minimality among positive feasible label bounds.

## Cycle-star graphs

Section 1, printed page 727:

> The *cycle-star* graph, written $CS_{k,n-k}$, is a graph with $n$ vertices consisting of the cycle graph of length $k$ and $n-k$ leafs appended to the same vertex of the cycle.

The source gives

$$V(CS_{k,n-k})=\{v,v_i: 1 \leq i \leq n-1 \};$$

$$E(CS_{k,n-k})=\{vv_i:1\leq i\leq n-k\}\cup\{vv_{n-k+1},vv_{n-1}\}\cup\{v_iv_{i+1}:n-k+1\leq i\leq n-2\}.$$

The formal carrier is `Fin n`: vertex zero represents $v$, and positive
index $i$ represents $v_i$. `SimpleGraph.fromRel` symmetrizes the displayed
edge relation and excludes loops.

## Conjecture 3.1

End of Section 3, printed page 738:

> Let $G=CS_{k,n-k}$ be a cycle-star graph. For $k \geq 8$ and $n-k \geq 1$,
>
> $$es(G):=\begin{cases}\lceil\frac{n+1}{2}\rceil&\text{for }k+1\leq n\leq 2k-4,\\n-k+2&\text{for }n\geq 2k-3.\end{cases}$$

For natural $n$, `(n + 2) / 2` is the source ceiling. Both source ranges
remain separate implications under the two common hypotheses.

## Proof and scope

The construction sets the common vertex label to $K$. Consecutive labels
on the internal path have sums $j+1$ until $j=K-1$, then $j+2$ when the
smaller-bound branch applies. The omitted sum $K+1$ closes one end of the
cycle. The other closing edge and all leaf edges have larger sums;
skipping the other endpoint label keeps them distinct. Degree and edge
count give the matching lower bounds.

Issue #22868 supplies the statement echo, experiment pin and partial
literature screen. The experiment is in
`the-omega-institute/trureturing-experiments`, commit
`bca5cba400e427feb7569b21bc7c0ae894a85c1a`, at
`docs/reports/salma-nagesh-narahari-cycle-star-irregularity/check.py`,
SHA256 `efc70ce44faa45b882da37acc809ea2a4bfd4d6a8421b1482db217f4fdaad226`.
Its reported Python exit code is 0; finite checks do not prove an
unbounded statement.

The four-slot escape audit for the public settling theorem is unfinished:
https://github.com/the-omega-institute/trureturing/issues/23027.

Literature completeness is ASSUMED-UNVERIFIED. Complete primary theorem
screens remain unverified for DOI 10.1007/s44427-026-00036-5,
10.1142/S1793830925501423, 10.1016/j.amc.2014.06.028 and
10.37256/cm.6120255957. No claim about other graph operations, products
or powers follows from this settlement.
