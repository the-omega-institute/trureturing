---
bibkey: aceskalortripperger2026ornaments
authors: Roza Aceska; McKailyn Lort; Allison Ripperger
year: 2026
title: Ornaments and Difference Distance Magic Oriented Graphs
doi: 10.48550/arXiv.2606.16001
url: https://arxiv.org/abs/2606.16001v3
claim: "The conclusion conjectures that the connected 14-vertex, 24-edge DDMOG in Figure 6 has the fewest edges among connected 14-vertex DDMOGs."
strata_touched:
  - D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2606.16001

Source: https://arxiv.org/abs/2606.16001v3

## Source definitions

Section 1.1, pages 1–2:

> The in-neighborhood of a vertex $v$ is the set of vertices $u \in V(D)$ such that $(u,v) \in E(D)$ and is denoted $N^+(v)$.

> The out-neighborhood of a vertex $v$ is the set of vertices $u \in V(D)$ such that $(v,u) \in E(D)$ and is denoted $N^-(v)$.

> An oriented graph $\overrightarrow{G}$ is a digraph such that $(u,v) \in E(\overrightarrow{G})$ implies $(v,u) \not\in E(\overrightarrow{G})$.

> The underlying graph $G$ of a digraph $D$ is the graph such that 1. $V(G)=V(D)$, and 2. if $(u,v) \in E(D)$ or $(v,u) \in E(D)$, then $uv \in E(G)$.

Page 2:

> The weight of vertex $x$ is defined [2] as the sum of the vertex labels directed into $x$ minus the sum of vertex labels directed out of $x$,
>
> $$\text{wt}(x)=\sum_{y\in N^+(x)}f(y)-\sum_{y\in N^-(x)}f(y).$$

> A difference distance magic (DDM) labeling [2] of an oriented graph $\overrightarrow{G}$ with $n$ vertices is a bijection $f:V(\overrightarrow{G})\rightarrow\{1,2,...,n\}$ where there exists some $k\in\mathbb{N}$ such that for all $x\in V(\overrightarrow{G})$ $\text{wt}_f(x)=k$; it shows that $k=0$ for all $x\in V(\overrightarrow{G})$.

> If an oriented graph $\overrightarrow{G}$ has a DDM labeling then we say that $\overrightarrow{G}$ is a difference distance magic oriented graph (DDMOG).

## Fourteen-vertex conjecture

Conclusion, page 25:

> Another question we have encountered as we were writing this paper is related to the minimal number of edges a connected DDMOG with $n$ vertices must have: What is the sparsest connected DDMOG with $n$ vertices in terms of edges? When observing the DDMOG with $14$ vertices in Figure 6, we conjecture that it is the sparsest DDMOG with $14$ vertices.

Remark 2, page 9:

> This DDMOG has $14$ vertices and only $24$ edges - in comparison, the DDMOG $\overrightarrow{R_{14}}$ as defined in [1] via vertex coalescence has significantly more edges.

The quantified assertion uses `Fin 14`, integer labels, a bijection onto
`Set.Icc 1 14`, and an existential common natural weight. Connectivity is
connectivity of the undirected graph. Ordered-pair cardinality counts each
undirected edge once because asymmetric adjacency excludes loops and
opposite arcs. The source's Figure 6 construction remains an existence
example; its asserted edge minimality is refuted by the 23-edge certificate.

## Evidence and scope

Preregistered problem: https://github.com/the-omega-institute/trureturing/issues/25620.
The exact integer checker is in `the-omega-institute/trureturing-experiments`,
commit `2842b0dd76520525eb1ae93b26d3300b57c30a35`,
`docs/reports/aceska-lort-ripperger-sparsest-ddmog14/check.py`, SHA256
`b95354ce34512679e05903466fceca13e2a2184af52a25e008a263f33079f147`.
The command `python3 check.py` exits 0 and checks both Figure 6 and the
23-edge witness with exact integer arithmetic. It does not prove optimality
at 23 or an unbounded extremal formula.

The literature screen on issue #25620 found no settlement in the readable
scope. Literature completeness is ASSUMED-UNVERIFIED: citing-work indexes,
MathOverflow, MathDB, broad Zenodo and full-text searches include blocked or
rate-limited results. No claim of exhaustive novelty follows from the screen.
