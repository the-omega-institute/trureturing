---
bibkey: dovgosheyrovenska2026centraledges
authors: Oleksiy Dovgoshey and Olga Rovenska
year: 2026
title: On the Graph Corresponding to Center of Distances of Metric Space
doi: 10.48550/arXiv.2610.11596
url: https://arxiv.org/abs/2610.11596v1
claim: "Conjecture 4.2 characterizes three-central ultrametric edge minima against all metric spaces of the same order."
strata_touched:
  - D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2610.11596

Source: https://arxiv.org/abs/2610.11596v1

# Distance centers and Conjecture 4.2

### Definition 1.1, p. 1

> Let (Y,ρ) be a metric space. The center of distances of (Y,ρ) is the subset C(Y)⊆ℝ⁺, such that t∈ C(Y) if and only if the equation ρ(y,p)=t has a solution for every p∈ Y.

### Definition 1.2, p. 1

> Let (Y,ρ) be a metric space and let C(Y) be the center of distances of (Y,ρ). The central graph CG_Y of (Y,ρ) is a simple graph such that V(CG_Y)=Y and {u,v}∈ E(CG_Y) ⇔ ρ(u,v)∈ C(Y) for all u,v∈ Y. We will write that the central graph CG_Y is k-central if k=|C(Y)|.

### Definition 2.14, p. 4

> Let (Y,ρ) be a finite metric space with |Y|≥ 2. The diametrical graph G_Y of (Y,ρ) is a graph such that V(G)=Y and, for all u,v∈ Y, {u,v}∈ E(G_{Y}) ⇔ ρ(u,v)=diamY.

### Conjecture 4.2, p. 13

> Let (X,d) be a finite ultrametric space with |X|≥ 4, let the central graph CG_X be 3-central, and let G_X be the diametrical graph of (X,d). Then the following statements are equivalent. (i) The diametrical graph G_X is complete bipartite with parts X_1, X_2 satisfying the equality min{|X_1|,|X_2|}=2, and the central graph CG_X is the union G_X with star graphs S_1 and S_2, CG_X=G_X∪ S_1 ∪ S_2, such that V(S_1)=X_1 and V(S_2)=X_2. (ii) The inequality |E(CG_X)| ≤ |E(CG_Y)| holds for all metric spaces (Y,ρ) which have 3-central CG_Y and satisfy |Y|=|X|.

The source uses $\mathbb{R}^{+}=[0,\infty)$, including zero. Edges are
unordered pairs of distinct vertices. The Lean predicates use `MetricSpace`,
`SimpleGraph.fromRel`, `Metric.diam`, `completeBipartiteGraph`, subtype stars
mapped into the original carrier, and graph joins. `Nat.card` counts center
values and unordered edges. The comparator in clause (ii) has no ultrametric
hypothesis.

The four-point refutation uses the induced 2-adic metric on the values
$0,1,2,3$ and the induced real metric on $0,4,5,9$. Their centers are
$\{0,1/2,1\}$ and $\{0,4,5\}$, and their central graphs have six and four
edges, respectively. The first metric satisfies clause (i).

The literature screen recorded in issue #22906 found no settlement in its
specified sources. Completeness of that screen, including OpenAlex citation
coverage, is ASSUMED-UNVERIFIED. The restricted comparison with ultrametrics,
the sharp unrestricted lower bound and the all-order realization are not
settled by the Lean module.

The finite-family experiment is in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments),
commit `b43e249214c62d9db0aa173ebce49fee6c792470`, under
`docs/reports/central-distance-ultrametric-edges/`. The recorded command is
`python3 docs/reports/central-distance-ultrametric-edges/check.py`; its exit code
is 0 and its final line is `ALL_CHECKS_OK`. The checker SHA256 is
`632f89f2254e25666c83fff36e78c82d263199b8f0f2091484c1bc4378b56005`.
It checks the separate all-order construction for orders 4 through 32 using
exact rational arithmetic. These finite computations do not establish the
unbounded statements in Lean.
