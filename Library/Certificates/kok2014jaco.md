---
bibkey: kok2014jaco
authors: Johan Kok, Paul Fisher, Bettina Wilkens, Mokhwetha Mabula, Vivian Mukungunugwa
year: 2014
title: Characteristics of Jaco Graphs, J_infinity(a), a in N
doi: null
url: https://arxiv.org/abs/1404.1714v1
claim: Proposition 4.4 conjectures the equivalence of both adjacent infinite-outdegree inequalities and both adjacent shortest-directed-path-count inequalities for every k at least seven in every Fibonacci bracket.
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
license: citation-only
triage: anchor
---

# The original directed Jaco path-count question

Source: https://arxiv.org/abs/1404.1714v1, Section 4, Proposition 4.4 and
the final open-problem list. All five authors are listed above in source
order. The versioned original source is distinct from the later Jaco
integer-sequence paper.

Proposition 4.4 states:

> Let $k \geq 7$ and $f_i < k \leq f_{i+1}$, and $f_i,f_{i+1} \in \mathbb{F}$.
> If and only if $d^+(v_k)$ is non-repetitive (meaning
> $d^+(v_{k-1}) \neq d^+(v_k) \neq d^+(v_{k+1})$) then $\psi(v_k)$ is
> non-repetitive (meaning
> $\psi(v_{k-1}) \neq \psi(v_k) \neq \psi(v_{k+1})$).

Its proof placeholder is “(Conjectured)”, and the source explicitly asks
“[Open problem: Prove Proposition 4.4]”. Each chained inequality denotes
the conjunction of its two adjacent comparisons, with no comparison
required between the first and third terms. The full question universally
quantifies every $k \geq 7$ and every bracket index $i$ satisfying
$f_i < k \leq f_{i+1}$.

The infinite directed graph has positive labels and an arc $(v_h,v_j)$
exactly when $h<j$ and $j\leq (a+1)h-d^-(v_h)$. At $a=1$ its right
endpoint is $2h-d^-(v_h)$. The finite graph $J_n(1)$ retains vertices
$1,\ldots,n$ and these forward arcs. The degree $d^+(v_h)$ is the full
infinite outdegree. The quantity $\psi(v_n)$ is the number of distinct
shortest directed paths from $v_1$ to $v_n$ in $J_n(1)$; every endpoint
uses its own finite truncation and path length counts edges. An undirected
graph or a count defined by a recurrence would change the question.
The formal result does not use the converse of Proposition 4.3.

## Verified locator

https://arxiv.org/abs/1404.1714v1, Section 4, Proposition 4.4, states the
full all-index equivalence quoted above. Its proof is marked
“(Conjectured)”. The authors list “[Open problem: Prove Proposition 4.4]”
in the final open-problem list. This locator identifies the original
author-posed question; it does not establish worldwide solution status
or priority.

## Bounded literature scope

The inspected material comprises arXiv:1404.0484v1, arXiv:1506.06538v1,
arXiv:2507.16500v1, an eighteen-record arXiv Jaco-title catalog, a five-result
OpenAlex screen, displayed domination material, critical-review metadata
and bibliography, linear-Jaco landing material and a preface. No
whole-equivalent answer was authenticated in this bounded material.
Matching MathDB answer bodies were not acquired: the public entry and
supplied access clue returned HTTP 403 with a Cloudflare challenge.
Semantic Scholar and a public search index returned HTTP 429; another
public index returned HTTP 500. Search-engine challenges and unread
journal or follow-up full texts remain gaps. These observations establish
neither worldwide absence of an earlier solution nor novelty or priority.
The original paper itself explicitly poses the question as open.
