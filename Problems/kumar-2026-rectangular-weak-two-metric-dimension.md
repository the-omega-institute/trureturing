---
slug: kumar-2026-rectangular-weak-two-metric-dimension
bibkey: kumar2026weakmetric
doi: 10.48550/arXiv.2609.32161
url: https://arxiv.org/abs/2609.32161v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.result
---

# Kumar's remaining rectangular weak two-metric dimensions

## Problem

Aryan Kumar, arXiv:2609.32161v1, §7:

> The rectangular k = 2 values below the threshold m = 2n − 2 remain to be determined.

The vertices of $K_n\square K_m$ are pairs in $[n]\times[m]$, with
$d((i,j),(a,b))=[i\ne a]+[j\ne b]$. For a landmark set $S$, put
$\Delta_S(x,y)=\sum_{w\in S}|d(x,w)-d(y,w)|$.
A weak $k$-resolving set has $\Delta_S(x,y)\ge k$ for every distinct pair;
$\operatorname{wdim}_k$ is its least cardinality.

The exact rectangular answer is

$$
\operatorname{wdim}_2(K_n\square K_m)
=\min\left\{\left\lceil\frac{2(n+m)}3\right\rceil,\,2n-2\right\}
\qquad(4\le n<m<2n-2).
$$

For natural-number division, the ceiling is $(2(n+m)+2)/3$.
The Lean `claim` retains all three size conditions and both upper-bound terms.

## Motivation

The source's Theorem 2.10 gives dimension $m$ when $m\ge2n-2$ and the lower
bound $m+1$ when $3\le m\le2n-3$. The formula determines the remaining
strictly rectangular values, including the transition between the two
optimal landmark constructions.

## Gap

Kumar (arXiv:2609.32161v1, 2026) proves $\operatorname{wdim}_2(K_n\square K_m)=m$ for $m\ge2n-2$ and $\operatorname{wdim}_2\ge m+1$ for $3\le m\le2n-3$, and lists the values for $n<m<2n-2$ as undetermined in §7. Fernández, Klavžar, Kuziak, Muñoz-Márquez and Yero (arXiv:2505.19642) leave the rectangular case $k=2$ for further investigation and report integer-programming values for $n\le8$; all fourteen of their values with $n<m<2n-2$ agree with the formula proved here. arXiv lists only version 1 of 2609.32161 and no citing work; an arXiv search for "weak k-metric" returns only 2505.19642, 2605.22307 and 2609.32161; the MathDB entry #368568 concerns $k\ge3$.

## Route

Write $g_i$ and $h_j$ for the landmark counts in row $i$ and column $j$.
Pairs in one row have separation $h_j+h_{j'}$; pairs in one column have
separation $g_i+g_{i'}$. For $i\ne i'$ and $j\ne j'$,

$$
\Delta_S((i,j),(i',j'))+2[(i,j')\in S]+2[(i',j)\in S]
=g_i+g_{i'}+h_j+h_{j'}.
$$

Consequently the row and column degree sums must be at least two.
Two vertex-disjoint landmark edges must have total endpoint degree at least
six. These three conditions also suffice: when both cross corners are
landmarks, the third condition applies; with zero or one cross landmark,
the first two conditions suffice. This includes empty rows and columns.

For the lower bound, an empty row forces every other row to have degree at
least two, giving $|S|\ge2n-2$. An empty column similarly gives
$|S|\ge2m-2\ge2n-2$. Otherwise all degrees are positive and the exact
incidence count is

$$
n+m=\sum_{(i,j)\in S}\left(\frac1{g_i}+\frac1{h_j}\right).
$$

If there is no edge with both endpoint degrees one, each summand is at most
$3/2$, so $2(n+m)\le3|S|$. If an edge has both degrees one, every other
edge is disjoint from it and has endpoint-degree sum at least four. Its
charge is therefore at most $4/3$. Thus
$n+m\le2+4(|S|-1)/3$, or $3(n+m)\le4|S|+2$.
For $n+m\ge6$ this again implies $2(n+m)\le3|S|$.
Taking the integer ceiling proves the lower bound.

For the upper bound $2n-2$, leave row zero empty. Index $2(n-1)$ landmarks
by $q=0,\ldots,2(n-1)-1$ and place landmark $q$ in row
$\lfloor q/2\rfloor+1$ and column $q\bmod m$. Every occupied row has
degree two, and every column is occupied because $m\le2(n-1)$.
Every two disjoint landmark edges therefore have endpoint-degree total at
least six, and the degree conditions hold.

For the ceiling upper bound, construct an incidence forest for positive
$n,m$ with $n\le2m$, $m\le2n$ and $n+m\ge3$. For totals at most five,
use a three-vertex star, a four-vertex path, or a five-vertex path.
For larger totals, if $n\le m$, remove one row and two columns, construct
the smaller forest, and adjoin a disjoint three-vertex star centered in
the new row. If $m<n$, use the symmetric construction. The reduced sizes
retain the balance conditions. Each step adds three vertices and two edges,
so the total edge count is at most $\lceil2(n+m)/3\rceil$.
Every row and column has positive degree, and every edge has endpoint-degree
sum at least three. The resolving conditions follow.

## Falsifier

The formula would fail if the distance identities were incorrect, an empty
row or column evaded the degree lower bound, the reciprocal charges exceeded
their stated bounds, or either construction violated its cardinality or
separation conditions. The distance identities count both cross corners,
and the constructions retain every row and column condition needed for
all distinct vertex pairs.

## Evidence

The designated statement is
`D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.result : claim`.
The core definitions use `Fin n × Fin m`, finite landmark sums and the
infimum of achievable natural cardinalities. The complete vertex set is
weak two-resolving for every pair of natural sizes, so the minimum at
$k=2$ is attained even for empty or singleton vertex products.

The lower estimate uses exact rational arithmetic and finite incidence
counts. The upper estimates use symbolic finite embeddings and natural
arithmetic. No approximate optimization or floating-point premise is needed.
The axiom closure of `result` is `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, new axiom or `native_decide` is used.

## Triage

- [proved: `HammingWeakTwoMetricDimension.result`] The formula determines
  every strictly rectangular value below the source threshold. The two
  competing mechanisms are a sparse incidence forest covering all vertices
  and a configuration with one empty row. The smaller of their landmark
  counts is optimal.
- [proved: `HammingWeakTwoMetricDimensionLower.bipartite_degree_charging`]
  The nonisolated-vertex incidence estimate only needs at least six total
  vertices and the disjoint-edge endpoint-degree condition; connected
  components need not be classified.
- [open] The source's questions for $k\ge3$ and the square case are separate
  boundaries. The rectangular formula alone supplies no general solution
  for those parameters.

## ASSUMED-UNVERIFIED

Forward citations were screened through arXiv, Semantic Scholar, MathDB and web search only; no citation index was read exhaustively.
