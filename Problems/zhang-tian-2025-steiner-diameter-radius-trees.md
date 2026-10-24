---
slug: zhang-tian-2025-steiner-diameter-radius-trees
bibkey: zhangtian2025steinerradius
doi: 10.48550/arXiv.2511.22492
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.result
---

# Zhang–Tian Conjecture 5.1: Steiner diameter and anchored radius of trees

## Problem

Qingnan Zhang and Yingzhi Tian, *On the Steiner k-diameter and Steiner
(k, k′)-radius of trees*, arXiv:2511.22492v1, p. 14, Conjecture 5.1, states:

> Let n, k, k′ be integers with n ≥ k ≥ 3 and k > k′ ≥ 1 and let T be a tree with order n. Then Sd_k(T) ≤ k/(k − k′) Sr_{k,k′}(T) − k′(k′ − 1)/(k − k′).

Here $d_T(S)$ is the minimum edge count among connected subgraphs containing
$S$; $\varepsilon_k(v;T)$ maximizes $d_T(S)$ over $k$-sets containing $v$;
$Sd_k(T)$ maximizes these vertex eccentricities.
For an anchor set $B$, $\varepsilon_{k,r}(B;T)$ maximizes $d_T(S)$ over
$k$-sets containing $B$, and $Sr_{k,r}(T)$ minimizes this quantity over
$r$-sets $B$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A finite simple tree of order $n$ | `V : Type`, `Fintype V`, `DecidableEq V`, `T : SimpleGraph V`, `T.IsTree`; $n$ is `Fintype.card V` | Exact; decidable equality is classical bookkeeping on a finite carrier. |
| $n\ge k\ge3$ | `k ≤ Fintype.card V`, `3 ≤ k` | Exact. |
| $k>k'\ge1$ | `r < k`, `1 ≤ r` | Exact; $r$ denotes $k'$. |
| Minimum connected-subgraph edge count | `steinerDist` | Literal source definition, using a natural infimum. |
| Vertex eccentricity and diameter | `steinerEcc`, `steinerDiam` | Literal nested maxima, as natural suprema. |
| Anchored eccentricity and radius | `steinerSetEcc`, `steinerRadius` | Literal extrema over terminal sets of the specified cardinality. |
| The rational inequality | `claim`, proved by `result` | All distances and parameters are cast into $\mathbb Q$ before subtraction and division. |
| Auxiliary cut representation | `Separates`, `cutEdges`, `steinerDist_cut` | Repository-derived objects characterize the source's literal distance; they do not replace its definition. |
| Arbitrary terminal $k$-set $A$ and anchor $r$-set $B$ | `pointwise_bound` | Strengthening; no disjointness, hull containment or diameter-maximization hypothesis. |

## Motivation

The settling declaration is
`D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.result`.
It proves the conjecture for all finite trees and all source parameters.
The public theorem `pointwise_bound` gives the stronger estimate

$$(k-r)d_T(A)+r d_T(B)\le k\varepsilon_{k,r}(B;T)$$

for every $k$-set $A$ and $r$-set $B$, provided $1\le r<k\le n$.

## Gap

This is a tier-1 externally named conjecture, preregistered in
[issue #20671](https://github.com/the-omega-institute/trureturing/issues/20671).
That issue records the source and literal Lean conventions, a proof route,
and a bounded literature screen. The reported arXiv, MathDB 371714,
title/identifier/author/topic and formal-conjectures searches found no
settlement in their searched scope. The listed later Tian papers contain no
Steiner material. Full texts by X. Li (Axioms 2025), Reiswig (DAM 2024),
Li–Zeng–Pan–Li (DAM 2024), and Zeng–Li (DAM 2026) remain unread in that screen.
Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

`steinerDist_cut` identifies the defining distance with the number of edges
whose deletion separates two terminals. The private connected hull supplies
the minimum connected subgraph. Its cut characterization constructs the
component containing a chosen terminal after an edge is deleted.

For $H=H(A)$, $J=H(B)$ and $s=k-r$, every edge of $J$ survives in every
$H(B\cup X)$ for an $s$-subset $X$ of $A$. For an edge of
$H\setminus J$, a terminal across that cut forces survival when it is
selected. The fraction of $s$-subsets containing any fixed terminal is $s/k$.
Double counting gives

$$\varepsilon_{k,r}(B;T)\ge |E(J)|+
\frac{k-r}{k}\bigl(|E(H)|-|E(H)\cap E(J)|\bigr)
\ge\frac{k-r}{k}d_T(A)+\frac r k d_T(B).$$

This display explains the estimate proved by `pointwise_bound`; the proof
uses natural-valued binomial counts before rational division.
The private `steinerDist_lower` proves $|B|-1\le d_T(B)$.
The private `diameter_attained` and `radius_attained` supply extremizers;
`conjecture_nat` and `result` give the conjectured inequality.

## Falsifier

The formal target has every source hypothesis and the full rational
conclusion. A source-level counterexample would be a finite tree with
$1\le r<k\le n$, $k\ge3$, and
$(k-r)Sd_k(T)+r(r-1)>kSr_{k,r}(T)$.
The public `result` rules out such a counterexample in the stated model.
The extension to arbitrary connected graphs is open here.

## Evidence

The mathematical module is
`D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.lean`,
with its corresponding Blueprint Scribe and emitted Markdown.
It imports only pinned Mathlib. The module's admission basis is
`open-problem-resolution (#20671; Proved)`; its utility is `none`.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

### Independent computation

[Published checker and output](https://github.com/the-omega-institute/trureturing-experiments/tree/e0ac6603671f2724ed314fd45eca3383b063a589/docs/reports/zhang-tian-2025-steiner-diameter-radius-trees).
Command: `python3 docs/reports/zhang-tian-2025-steiner-diameter-radius-trees/check.py`
from that experiments-repository revision; exit 0.
Script SHA-256: `c9f56ed496fd34dd7317501871c6fc798c5726c8d97d1c55d3690abbe54b711f`.
The computation reproduces the six equality examples listed below and tests
all 985 nonisomorphic trees with $3\le n\le12$, all $3\le k\le n$ and
$1\le r<k$: 55,778 parameter instances, zero failures of Conjecture 5.1
or Theorem 3.4, and 16,847,366 pointwise checks with zero failures.
These are finite computations, separate from the universal kernel proof.

### Escape audit

The escape audit is unfinished for `steinerDist_cut`, `pointwise_bound`
and `result`; see
[issue #20778](https://github.com/the-omega-institute/trureturing/issues/20778).
The attempted dependent-family readouts lack compiled rejected-realization,
variation, sensitivity, observational-dependence and source-binding evidence.
No successful Reg mirror is retained and no registration is asserted
`declared_validated`.

### Declaration judgement

| Declaration | proof_shape | escape_witness | Direct consumer(s) | Direct frozen dependencies |
| --- | --- | --- | --- | --- |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.path_le_connected` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.subset_hull` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_le` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_mono`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_cut`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower`, `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_mono` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff` | content | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff` | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.cutEdges_eq_hull` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.cutEdges_eq_hull` | content | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff` | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_cut` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_cut` | content | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff` | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_mono` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_mono` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_mono` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_union_le_setEcc` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.setEcc_bdd` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_le_setEcc` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_le_setEcc` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_union_le_setEcc` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_union_le_setEcc` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.separates_mono` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.cutEdges_mono` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.cutEdges_mono` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.opposite_terminal` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.count_subsets_containing` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.finite_averaging` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.finite_averaging` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | content | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.diameter_attained` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.radius_attained` | bind-only | none | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat` | content | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.result` | None |
| `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.result` | content | `D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound` | None (settling result) | None |


## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and scope |
| --- | --- | --- |
| Anchor-hull mechanism and additive correction | Proved; kernel-checked `pointwise_bound`, `conjecture_nat`, `result` | The full anchor hull persists. The overlap term is bounded by its size; no disjointness or containment of hulls is needed. The cardinal lower bound supplies $r(r-1)$. |
| Pointwise scope and endpoints | Proved; kernel-checked `pointwise_bound` | $A$ is any $k$-set, and $B$ is any $r$-set. Both $r=1$ and $r=k-1$ satisfy its hypotheses. |
| Six equality examples and exhaustive finite screen | Computed; the independent computation entry | $P_2(2,2;2)$ at $k=4$, $P_2(3,2;1)$ at $k=5$, $P_2(2,2;1)$ at $k=4$, $P_3(2,2;2)$ at $k=4$, $P_3(3,3;1)$ at $k=6$, and $P_3(3,2;1)$ at $k=5$ reproduce $Sd_k=kx+r-1$ and $Sr_{k,r}=(k-r)x+r-1$. The finite screen has the tested scope stated in Evidence. |
| Equality classification and weighted trees | Open | A full equality classification, including extremal trees for $r\ge4$, and a nonnegative-weighted-tree version are not formalized. Numerical equality counts do not classify the universal family. |
| Effect on the source's later results | Source-checked; arXiv:2511.22492v1, p. 14 | Conjecture 5.1 is followed directly by References. There is no subsequent source theorem whose proof requires updating. |
| General connected graphs | Open | The argument uses unique tree paths and the cut characterization; no general connected-graph conclusion is asserted. |

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not established.
The unread full texts named in Gap remain outside the literature screen.
The experiments establish only their finite tested scope.
Four-slot escape-registration evidence is incomplete as disclosed in
issue #20778; it is distinct from the kernel-checked mathematical result.
