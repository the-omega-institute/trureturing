---
slug: huang-stoica-xia-zhong-2020-tree-equations-nonconstant
bibkey: huangstoicaxiazhong2020einstein
doi: null
url: https://arxiv.org/abs/2006.06716v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.result
---

# The Huang–Stoica–Xia–Zhong conjecture on $T_2$ is refuted

## Problem

A. Huang, B. Stoica, X. Xia and X. Zhong, *Bounds on the Ricci curvature and solutions to the Einstein equations for weighted graphs*, arXiv:2006.06716v1 (2020), define the tree equation of motion using the shortest-path lengths $P_{ij}$ and the vertex sums $c_i$ and $d_i$. For an edge $ij$ they write
$$
\mathrm{tEoM}_{ij}
=\frac{1}{P_{ij}}\left(\frac{c_i^2}{d_i^2}+\frac{c_j^2}{d_j^2}\right)
-\frac{c_i}{d_i}-\frac{c_j}{d_j}=0.
$$
For a tree, they identify $P_{ij}$ on an edge with its edge length, and use $d_i=\sum_{i'\sim i}P_{ii'}^{-2}$ and $c_i=\sum_{i'\sim i}P_{ii'}^{-1}$. They define $T_q$ as the infinite tree whose vertices have degree $q+1$, and call the setting with all edge lengths equal the constant solution. Section 5.2's second conjecture (ms.tex lines 1931–1934) asks:

> There exists no non-constant solution to the tEoM for $T_2$ with all edge lengths positive.

The Lean definition `claim` quantifies this assertion over every locally finite simple graph with decidable adjacency that is a tree, has degree $3$ at every vertex, and carries a symmetric positive edge-length function whose `tEoM` vanishes on every edge. It concludes that one real constant equals every edge length.

## Motivation

The conjecture would make the positive solutions of the tree equations on the 3-regular tree rigid: satisfying the edge equations would force one global edge length. A counterexample tests whether the local ratio $c_i/d_i$ can vary from vertex to vertex while the residual on each edge still vanishes. The paper's equation uses edge shortest-path lengths on a tree, so the formal setting records the edge values of the length function and the same reciprocal and reciprocal-square neighbour sums.

## Gap

The preregistration in issue [#25434](https://github.com/the-omega-institute/trureturing/issues/25434) records the source reading, the exact universal statement, the cubic-tree route, and the checks for a positive nonconstant construction. Its bounded literature check found the conjecture in arXiv v1, no settlement in the searched citing works, and no repository record; it also records that earlier odd-degree constructions do not cover $q=2$.

`not-found-in-searched-scope`.

## Route

1. The construction uses the vertex type $\mathbb Z \oplus (\mathbb Z\times\operatorname{List}(\mathrm{Bool}))$. The private `parent` lowers the integer rank by one, and `graph` declares two vertices adjacent exactly when one is the parent of the other. `graph_finite` supplies the `graph.LocallyFinite` instance. `graph_tree` proves `graph.IsTree`, and `graph_degree (i)` proves `graph.degree i = 3` for every vertex $i$.
2. The private `lengths` assigns $(5/3)2^{\min(n,m)}$ on a spine edge between $v_n$ and $v_m$, and $2^n$ to branch edges in the branch rooted at $v_n$, with a symmetric definition on all ordered pairs. `lengths_symmetric (i j)` assumes `graph.Adj i j` and proves `lengths i j = lengths j i`; `lengths_positive (i j)` assumes `graph.Adj i j` and proves $0<\mathrm{lengths}\ i\ j$.
3. `ratio_spine (n)` proves that `ratio graph lengths (Sum.inl n) = 2^n`. `ratio_branch (n) (w)` proves that `ratio graph lengths (Sum.inr (n,w)) = 2^n`. Thus the branch edges have equal endpoint ratios, while a spine edge between successive spine vertices has ratios $2^n$ and $2^{n+1}$.
4. `residuals (i j)` assumes `graph.Adj i j` and proves `tEoM graph lengths i j = 0`. It handles an edge oriented from a vertex to its predecessor, using the two ratio lemmas and the explicit edge lengths, and obtains the reverse orientation from `lengths_symmetric` and the already proved predecessor residual.
5. `nonconstant` assumes $\exists c,\ \forall i\,j,\ \mathrm{graph.Adj}\ i\ j\to\mathrm{lengths}\ i\ j=c$ and derives a contradiction from the adjacent attachment edge of length $1$ and the adjacent spine edge of length $5/3$. The theorem `result` runs under `classical`, supplies the required decidable adjacency instance, and applies the alleged `claim` to `graph`, `graph_tree`, `graph_degree`, `lengths`, `lengths_symmetric`, `lengths_positive`, and `residuals`; `nonconstant` then proves the resulting contradiction.

## Falsifier

The settlement would not address the paper's question if the formal graph were not a locally finite tree of degree $3$, if the edge lengths were not symmetric and positive on adjacent vertices, if the residual vanished only on some edges, or if all edge lengths were equal. Those conditions are discharged by `graph_tree`, `graph_degree`, `lengths_symmetric`, `lengths_positive`, `residuals`, and `nonconstant` with the hypotheses stated in the route. It would also be a mismatch if the paper's $P_{ij}$ on adjacent vertices did not equal the assigned edge length; the source's tree setting identifies those quantities, while this module does not formalize a separate shortest-path theorem. No boundary condition or uniform positive lower bound is part of the formal `claim`.

## Evidence

The canonical source is `D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:66044a0014de6a25c523c1d2d27edcf96115232e65963984addc075b22766d54`;
- `claim`: `sha256:554248a0651ad29d763e9b172a8cbbab285e6c4580af092592f6481816037f6b`.

- **Proof.** `result` has type `¬ claim`; its proof instantiates the quantified claim with the explicit cubic tree and length function, proves the tree, degree, symmetry, positivity, and edge-residual conditions, and applies `nonconstant`.
- **Axioms.** `result` depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1: a conjecture stated in a 2020 arXiv paper (arXiv v1 only, no journal reference), preregistered in issue #25434 before any Lean.  
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal `claim` is false. There is a locally finite simple tree with decidable adjacency, degree $3$ at every vertex, and a symmetric positive edge-length function whose `tEoM` is zero on every edge although no single real constant equals all edge lengths. The formal witness is a bi-infinite spine with a rooted binary branch at each spine vertex: the spine edge $v_n\sim v_{n+1}$ has length $(5/3)2^n$, every edge in the branch rooted at $v_n$ has length $2^n$, and the formal ratio lemmas give $c_i/d_i=2^n$ at every vertex in that branch and at $v_n$. The formal residual calculation gives zero on both edge types, while the attachment edge at $v_0$ has length $1$ and the spine edge $v_0\sim v_1$ has length $5/3$. The same witness has three equal incident edges at a branch vertex while remaining globally nonconstant, so it also supplies the ingredients for a counterexample to the preceding source assertion: “For $T_q$, if a setting $M_q$ is a solution to the tEoM with positive edge lengths for all edges and there exists a vertex $i \in T_q$ such that all edges connected to $i$ are equal, then $M_q$ is a constant solution.” That assertion is not a separate Lean declaration here.

**Computed, not formalized:** None.

**Argued, not formalized.**
- The failure mechanism is scale variation along the spine: choosing $s_n=2^n$ makes the ratio field change by a factor of $2$ from one spine level to the next, while the coefficient $5/3$ makes the spine residual cancel; equal-ratio branch edges cancel directly. This explains why positivity alone does not force a global constant.
- A restriction involving constant boundary data or another global compatibility condition could remove this scaling freedom, but whether it suffices for uniqueness is open here and no repaired statement is proved.
- The source's earlier constant-boundary uniqueness results, its $T_1$ and odd-$q$ constructions, and its curvature bounds are not settled by this result. Their dependence on the refuted no-solution conjecture and any consequent changes are open here; this module supplies no downstream derivation.

## ASSUMED-UNVERIFIED

The literature search recorded in issue #25434 is bounded and does not establish exhaustive worldwide novelty or priority; the cited-work search and MathDB report were not independently reproduced in this seat. The identification of the paper's named $T_2$ with the universal cubic-tree formulation is not separately formalized in this module. The generalized $q,r$ family, the preceding conjecture, the proposed repaired restrictions, and the effects on the paper's other statements are not formalized beyond the declarations identified above.
