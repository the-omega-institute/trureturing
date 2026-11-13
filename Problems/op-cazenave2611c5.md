---
slug: op-cazenave2611c5
bibkey: cazenave2026spectralgraphconjectures
doi: null
url: https://arxiv.org/abs/2611.03879v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.result
---

# Cazenave Conjecture 5: the Laplacian–rank bound

## Problem

Tristan Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*,
arXiv:2611.03879v1, Section 7, Conjecture 5 (#239534), states:

> $\mu_2+\operatorname{rk}(A)\le2m$.

Section 1 restricts graphs to simple, undirected and connected graphs on
at least two vertices. The Laplacian is $L=D-A$, its real eigenvalues are
listed in decreasing order with multiplicity, $A$ is the adjacency matrix,
and $m$ counts unordered edges once. The source TeX locators are
main.tex:48–69 and 752–756. The v1 source archive has SHA-256
aebb9213f3b0158c9b0dc52155886fcc663a830367bdad713a9133eb52729975.
Preregistration: [#26564](https://github.com/the-omega-institute/trureturing/issues/26564).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every finite order at least two | Natural parameter n and carrier Fin (n + 2) |
| Simple and undirected | SimpleGraph |
| Connected | G.Connected |
| Ordinary Laplacian D − A | G.lapMatrix Real in the reused lapEig definition |
| Second largest eigenvalue, with multiplicity | LinWangCaiBroomSpectralRatio.lapEig G 1 |
| Real adjacency rank | Real coercion of (G.adjMatrix Real).rank |
| Unordered edges, once each | G.edgeFinset.card |
| The complete inequality | result : claim |
| Decidable adjacency | Instance data for the same finite graph |

There is no graph-order cap, tree restriction, normalized spectrum,
absolute-value eigenvalue ordering, algebraic-connectivity replacement,
or extra spectral hypothesis. The statement has no division, inverse,
square root, logarithm, extremum or natural subtraction. Proof-only
division by two is over Real, and the nonzero-vector norm is proved
positive before cancellation.

## Motivation

The settling declaration is
D5.S3.Combinatorics.SpectralGraph.CazenaveLaplacianRankBound.result.
The admission basis is open-problem-resolution, using #26564. The
external named conjecture and its exact full scope supply that basis;
proof-shape classification remains a separate obligation.

## Gap

Equality classification and weighted or disconnected extensions are
outside this assertion. The source also mentions the matching-number
interpretation for trees. No matching-rank formula or stronger classical
tree theorem is required by this proof.

## Route

Write N for graph order. Positivity, decreasing eigenvalues and
tr(L)=2m give $\mu_2\le m$. Also rank(A)≤N. If m≥N, these bounds suffice.
Otherwise connectivity forces m=N−1 and the graph is a tree. When rank(A)<N,
rank(A)≤m again suffices.

In a full-rank tree of order at least three, an internal edge exists.
Indeed, the degree sum forces a vertex of degree at least two. If no
edge has two such endpoints, two of its neighbours have degree one and
have identical adjacency rows, contradicting full rank. Deleting an
internal bridge uv gives two sides of sizes p,q≥2 with p+q=N.
On x_u=x_v, the bridge contributes zero. The complete-side energy
identity bounds the quadratic form by max(p,q) times squared norm,
hence by (N−2) times squared norm. The top-two real spectral plane
contains a nonzero vector on this hyperplane. The decreasing spectral
basis bounds its Rayleigh quotient below by $\mu_2$, giving
$\mu_2\le N-2$. Combining with rank(A)≤N proves the target.
At order two the second largest Laplacian eigenvalue is zero.

The real lower-support Rayleigh estimate is reused in its original
LinWangCaiBroomSpectralRatio owner. The deletion-side partition and
crossing facts are reused from DePatraBridge and DePatraCounting;
these tracked suppliers are not described as frozen predecessors.

## Falsifier

A connected finite simple graph with the specified ordinary real
Laplacian spectrum and $\mu_2+\operatorname{rank}_{\mathbb R}(A)>2m$
would refute the assertion. A failure to elaborate this proof is a proof
gap, not a graph counterexample.

## Evidence

The D5 source, matching typed Scribe and shared source note carry the
mathematical statement and its correspondence. Kernel and axiom evidence
must cover the complete result and its actual import closure. The
unrestricted theorem cannot be replaced by finite checks.

The four-slot registration is unfinished under the linked-issue
exception in [#26564](https://github.com/the-omega-institute/trureturing/issues/26564).
No declared_validated registration is claimed. The missing evidence is a
faithful dependent-family realization retaining graph order, adjacency
instance and connectedness, its exact source reconstruction and bridge,
whole-family variation and sensitivity, and actual observational
dependence. The visibility-only exposure of rayleigh_ge_of_support also
requires its source-owner registration disposition.

## Triage

The contribution sought is settlement of the full named inequality.
Centroids, graph cuts, real spectral theory, the trace argument and
stronger classical tree bounds have prior art; they are not claimed as
new discoveries. Zhang's survey, arXiv:1111.2897v1, Theorem 4.1, attests
the stronger classical tree estimate $\mu_2\le\lceil N/2\rceil$.
That survey is secondary evidence; the original 1998 article was not
obtained in the bounded intake search.

No exact prior settlement was identified in the bounded searches
reported in #26564. Source-author archive openness is evidence about that
archive at intake, not worldwide priority. The source's equality
examples K2, K3 and P4 are not separately delivered as new theorems.
No conclusion about the source's other conjectures follows.

## ASSUMED-UNVERIFIED

Literature completeness, unindexed settlements, complete citing-work
enumeration and the unread classical originals remain
ASSUMED-UNVERIFIED within the bounds stated in #26564.
The registration evidence described above is unfinished.
